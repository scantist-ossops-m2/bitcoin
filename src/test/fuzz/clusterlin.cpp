// Copyright (c) 2020-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <test/fuzz/fuzz.h>
#include <test/fuzz/FuzzedDataProvider.h>
#include <util/strencodings.h>
#include <clusterlin.h>
#include <algorithm>
#include <vector>
#include <iostream>

using namespace clusterlin;

namespace {

using TestBitSet = BitSet<32>;

[[maybe_unused]] std::ostream& operator<<(std::ostream& o, const FeeFrac& data)
{
    if (data.IsEmpty()) {
        o << "()";
    } else {
        o << "(" << data.fee << "/" << data.size << "=" << ((double)data.fee / data.size) << ")";
    }
    return o;
}

[[maybe_unused]] std::ostream& operator<<(std::ostream& o, Span<const unsigned> data)
{
    o << '{';
    bool first = true;
    for (unsigned i : data) {
        if (first) {
            first = false;
        } else {
            o << ',';
        }
        o << i;
    }
    o << '}';
    return o;
}

[[maybe_unused]] std::ostream& operator<<(std::ostream& o, Span<const unsigned char> data)
{
    o << '{';
    bool first = true;
    for (unsigned i : data) {
        if (first) {
            first = false;
        } else {
            o << ',';
        }
        o << i;
    }
    o << '}';
    return o;
}

template<typename I>
std::ostream& operator<<(std::ostream& s, const bitset_detail::IntBitSet<I>& bs)
{
    s << "[";
    size_t cnt = 0;
    for (size_t i = 0; i < bs.Size(); ++i) {
        if (bs[i]) {
            if (cnt) s << ",";
            ++cnt;
            s << i;
        }
    }
    s << "]";
    return s;
}

template<typename I, unsigned N>
std::ostream& operator<<(std::ostream& s, const bitset_detail::MultiIntBitSet<I, N>& bs)
{
    s << "[";
    size_t cnt = 0;
    for (size_t i = 0; i < bs.Size(); ++i) {
        if (bs[i]) {
            if (cnt) s << ",";
            ++cnt;
            s << i;
        }
    }
    s << "]";
    return s;
}

/** String serialization for debug output of Cluster. */
template<typename S>
std::ostream& operator<<(std::ostream& o, const Cluster<S>& cluster)
{
    o << "Cluster{";
    for (size_t i = 0; i < cluster.size(); ++i) {
        if (i) o << ",";
        o << i << ":" << cluster[i].first << cluster[i].second;
    }
    o << "}";
    return o;
}

template<typename S>
std::ostream& operator<<(std::ostream& o, const DepGraph<S>& txgraph)
{
    o << "DepGraph{";
    for (size_t i = 0; i < txgraph.TxCount(); ++i) {
        if (i) o << ",";
        o << i << ":" << txgraph.FeeRate(i);
        S pars = txgraph.Ancestors(i);
        pars.Reset(i);
        for (auto j : pars) {
            if (pars[j]) {
                pars /= txgraph.Ancestors(j);
                pars.Set(j);
            }
        }
        o << pars;
    }
    o << "}";
    return o;
}

uint8_t ReadSpanByte(Span<const unsigned char>& data)
{
    if (data.empty()) return 0;
    uint8_t val = data[0];
    data = data.subspan(1);
    return val;
}

/** Deserialize a number, in little-endian 7 bit format, top bit set = more size. */
uint64_t ReadB128(Span<const unsigned char>& data, uint64_t mask = std::numeric_limits<uint64_t>::max())
{
    uint64_t ret{0};
    for (int i = 0; i < 10; ++i) {
        uint8_t b = ReadSpanByte(data);
        ret |= static_cast<uint64_t>(b & uint8_t{0x7F}) << (7 * i);
        if ((b & 0x80) == 0) break;
    }
    return ret & mask;
}

/** Variant of ReadB128 for signed integers. */
int64_t ReadB128Signed(Span<const unsigned char>& data, uint64_t mask = std::numeric_limits<int64_t>::max())
{
    uint64_t read = ReadB128(data, 2 * mask + 1);
    uint64_t shifted = (read + 1) >> 1;
    if (read & 1) {
        return -int64_t(shifted);
    } else {
        return shifted;
    }
}

/** Serialize a number, in little-endian 7 bit format, top bit set = more size. */
void WriteB128(uint64_t val, std::vector<unsigned char>& data)
{
    for (int i = 0; i < 10; ++i) {
        uint8_t b = (val >> (7 * i)) & 0x7F;
        val &= ~(uint64_t{0x7F} << (7 * i));
        if (val) {
            data.push_back(b | 0x80);
        } else {
            data.push_back(b);
            break;
        }
    }
}

/** Variant of WriteB128 for signed integers. */
void WriteB128Signed(int64_t val, std::vector<unsigned char>& data)
{
    if (val < 0) {
        WriteB128((uint64_t(-val) << 1) - 1, data);
    } else {
        WriteB128(uint64_t(val) << 1, data);
    }
}

template<typename BS>
bool CanAddDependency(const DepGraph<BS>& depgraph, unsigned parent, unsigned child)
{
    // If child is already a descendant of parent, the dependency would be redundant.
    if (depgraph.Descendants(parent)[child]) return false;
    // If child is already an ancestor of parent, the dependency would cause a cycle.
    if (depgraph.Ancestors(parent)[child]) return false;
    // If there is an ancestor of parent which is a direct parent of a descendant of child,
    // that dependency will have been redundant if a dependency between parent and child is
    // added.
    for (auto i : depgraph.Ancestors(parent)) {
        if (depgraph.Descendants(i) && depgraph.Descendants(child)) {
            if (depgraph.GetReducedChildren(i) && depgraph.Descendants(child)) return false;
        }
    }
    return true;
}

/** Deserialize a dependency graph. */
template<typename BS>
DepGraph<BS> ReadDepGraph(Span<const unsigned char>& data, unsigned maxsize = std::min<unsigned>(BS::Size(), 64))
{
    DepGraph<BS> ret;
    while (true) {
        // Read size.
        int32_t size = ReadB128(data, 0x7fffff);
        if (size == 0 || ret.TxCount() == maxsize) break;
        // Read fee.
        int64_t fee = ReadB128Signed(data, 0x7fffffffffffff);
        // Extend resulting graph with new transaction.
        unsigned idx = ret.TxCount();
        ret.entries.emplace_back(FeeFrac{fee, size}, BS::Singleton(idx), BS::Singleton(idx));
        // Read dependency information.
        uint64_t offset = 0;
        uint64_t counter = 0;
        for (unsigned loop = 0; loop < 2; ++loop) {
            bool done = false;
            for (unsigned i = 0; i < idx; ++i) {
                unsigned parent = loop ? idx : idx - 1 - i;
                unsigned child = loop ? idx - 1 - i : idx;
                if (CanAddDependency(ret, parent, child)) {
                    ++counter;
                    if (offset < counter) {
                        uint64_t diff = ReadB128(data);
                        offset += diff;
                        if (diff == 0 || offset < diff) {
                            done = true;
                            break;
                        }
                    }
                    if (offset == counter) {
                        ret.AddDependency(parent, child);
                    }
                }
            }
            if (done) break;
        }
    }
    return ret;
}

/** Convert a DepGraph back to a Cluster. */
template<typename BS>
Cluster<BS> DepGraphToCluster(const DepGraph<BS>& depgraph)
{
    Cluster<BS> ret(depgraph.TxCount());
    for (unsigned i = 0; i < ret.size(); ++i) {
        ret[i].first = depgraph.FeeRate(i);
        ret[i].second = depgraph.GetReducedParents(i);
    }
    return ret;
}

/** Serialize a dependency graph. */
template<typename BS>
void WriteDepGraph(const DepGraph<BS>& depgraph, std::vector<unsigned char>& data)
{
    DepGraph<BS> rebuild(depgraph.TxCount());
    for (unsigned idx = 0; idx < depgraph.TxCount(); ++idx) {
        // Write size.
        WriteB128(depgraph.FeeRate(idx).size, data);
        // Write fee.
        WriteB128Signed(depgraph.FeeRate(idx).fee, data);
        // Write dependency information.
        uint64_t offset{0}, counter{0};
        for (unsigned loop = 0; loop < 2; ++loop) {
            BS towrite = loop ? depgraph.GetReducedChildren(idx) : depgraph.GetReducedParents(idx);
            for (unsigned i = 0; i < idx; ++i) {
                unsigned parent = loop ? idx : idx - 1 - i;
                unsigned child = loop ? idx - 1 - i : idx;
                if (CanAddDependency(rebuild, parent, child)) {
                    ++counter;
                    if (towrite[idx - 1 - i]) {
                        rebuild.AddDependency(parent, child);
                        WriteB128(counter - offset, data);
                        offset = counter;
                    }
                }
            }
        }
        if (counter > offset) data.push_back(0);
    }
}

template<typename S>
S FindBestCandidateNaive(const DepGraph<S>& txgraph, const S& todo)
{
    // Queue of work units. Each consists of:
    // - inc: set of transactions definitely included
    // - und: set of transactions that can be added to inc still
    std::vector<std::pair<S, S>> queue;
    queue.emplace_back(S{}, todo);

    // Best solution so far.
    S best = todo;
    auto best_feerate = txgraph.FeeRate(todo);

    // Process the queue.
    while (!queue.empty()) {
        // Pop top element of the queue.
        auto [inc, und] = queue.back();
        queue.pop_back();
        // Look for a transaction to consider adding/removing.
        bool inc_none = inc.None();
        for (auto pivot : und) {
            if (inc_none || (inc && txgraph.Ancestors(pivot))) {
                // Add a queue entry with pivot included.
                auto new_inc = inc | (todo & txgraph.Ancestors(pivot));
                queue.emplace_back(new_inc, und / new_inc);
                // Add a queue entry with pivot excluded.
                queue.emplace_back(inc, und / txgraph.Descendants(pivot));
                // Update statistics to account for the candidate new_inc.
                auto new_inc_feerate = txgraph.FeeRate(new_inc);
                if (new_inc_feerate > best_feerate) {
                    best_feerate = new_inc_feerate;
                    best = new_inc;
                }
                break;
            }
        }
    }

    return best;
}

template<typename BS>
void SanityCheck(const DepGraph<BS>& depgraph)
{
    // Consistency check between ancestors internally.
    for (unsigned i = 0; i < depgraph.TxCount(); ++i) {
        // Transactions include themselves as ancestors.
        assert(depgraph.Ancestors(i)[i]);
        // If a is an ancestor of b, then b's ancestors include all of a's ancestors.
        for (auto a : depgraph.Ancestors(i)) {
            assert(depgraph.Ancestors(i) >> depgraph.Ancestors(a));
        }
    }
    // Consistency check between ancestors and descendants.
    for (unsigned i = 0; i < depgraph.TxCount(); ++i) {
        for (unsigned j = 0; j < depgraph.TxCount(); ++j) {
            assert(depgraph.entries[i].ancestors[j] == depgraph.entries[j].descendants[i]);
        }
    }
}

template<typename BS>
void MakeConnected(DepGraph<BS>& depgraph)
{
    auto todo = BS::Fill(depgraph.TxCount());
    auto comp = depgraph.FindConnectedComponent(todo);
    todo /= comp;
    while (todo.Any()) {
        auto nextcomp = depgraph.FindConnectedComponent(todo);
        depgraph.AddDependency(comp.Last(), nextcomp.First());
        todo /= nextcomp;
        comp = nextcomp;
    }
}

} // namespace

FUZZ_TARGET(clusterlin_adddependency)
{
    // Verify that computing a DepGraph from a cluster, or building it step by step using AddDependency,
    // have the same effect.

    // Construct a cluster of a certain length, with no dependencies.
    Cluster<TestBitSet> cluster;
    FuzzedDataProvider provider(buffer.data(), buffer.size());
    unsigned num_tx = provider.ConsumeIntegralInRange<unsigned>(2, 32);
    cluster.resize(num_tx);
    // Construct the corresponding DepGraph object (also no dependencies).
    DepGraph txgraph{cluster};
    // Read (parent, child) pairs, and add them to the cluster and txgraph.
    LIMITED_WHILE(provider.remaining_bytes() > 0, 1024) {
        unsigned parent = provider.ConsumeIntegralInRange<unsigned>(0, num_tx - 1);
        unsigned child = provider.ConsumeIntegralInRange<unsigned>(0, num_tx - 2);
        child += (child >= parent);
        cluster[child].second.Set(parent);
        txgraph.AddDependency(parent, child);
        SanityCheck(txgraph);
    }
    // Verify that the resulting DepGraph matches one recomputed from the cluster.
    assert(DepGraph{cluster} == txgraph);
}

FUZZ_TARGET(clusterlin_serialization)
{
    // Verify that any graph of transaction has its ancestry correctly computed by DepGraph, and if
    // it is a DAG, it can be serialized in a way that roundtrips.

    FuzzedDataProvider provider(buffer.data(), buffer.size());

    // Construct a cluster in a naive way (using a FuzzedDataProvider-based serialization).
    Cluster<TestBitSet> cluster;
    unsigned num_tx = provider.ConsumeIntegralInRange<unsigned>(1, 32);
    cluster.resize(num_tx);
    for (unsigned i = 0; i < num_tx; ++i) {
        cluster[i].first.size = provider.ConsumeIntegralInRange<int32_t>(1, 0x7fffff);
        cluster[i].first.fee = provider.ConsumeIntegralInRange<int64_t>(-0x80000000000000, 0x7fffffffffffff);
        for (unsigned j = 0; j < num_tx; ++j) {
            if (i == j) continue;
            if (provider.ConsumeBool()) cluster[i].second.Set(j);
        }
    }

    // Verify that ancestry is computed correctly.
    DepGraph depgraph(cluster);
    SanityCheck(depgraph);
    for (unsigned i = 0; i < num_tx; ++i) {
        //! Ancestors of transaction i.
        TestBitSet anc;
        // Start with being equal to just i itself.
        anc.Set(i);
        // Loop as long as more ancestors are being added.
        while (true) {
            bool changed{false};
            // For every known ancestor of i, include its parents into anc.
            for (auto i : anc) {
                if (!(cluster[i].second << anc)) {
                    changed = true;
                    anc |= cluster[i].second;
                }
            }
            if (!changed) break;
        }
        // Compare with depgraph.
        assert(depgraph.Ancestors(i) == anc);
    }

    // If the resulting graph is not a DAG, bail out.
    if (!depgraph.IsAcyclic()) return;

    // Check that serializing + deserializing results in an equivalent graph.
    std::vector<unsigned char> ser;
    WriteDepGraph(depgraph, ser);
    Span<const unsigned char> spanser(ser);
    auto decoded_depgraph = ReadDepGraph<TestBitSet>(spanser);
    SanityCheck(decoded_depgraph);
    assert(spanser.empty());
    assert(depgraph == decoded_depgraph);
}

FUZZ_TARGET(clusterlin_deserialization)
{
    // Construct a graph by deserializing.
    auto depgraph = ReadDepGraph<TestBitSet>(buffer);
    SanityCheck(depgraph);

    // Verify the graph is a DAG.
    assert(depgraph.IsAcyclic());

    // Verify the graph serializes and deserializes back to the same cluster.
    std::vector<unsigned char> ser;
    WriteDepGraph(depgraph, ser);
    Span<const unsigned char> serspan{ser};
    auto decoded_depgraph = ReadDepGraph<TestBitSet>(serspan);
    SanityCheck(decoded_depgraph);
    assert(depgraph == decoded_depgraph);
    assert(serspan.empty());
}

FUZZ_TARGET(clusterlin_make_connected)
{
    auto depgraph = ReadDepGraph<TestBitSet>(buffer);
    SanityCheck(depgraph);
    MakeConnected(depgraph);
    SanityCheck(depgraph);
    assert(depgraph.IsConnected());
}

FUZZ_TARGET(clusterlin_best_candidate)
{
    // Get RNG seed.
    uint64_t rng_seed = ReadB128(buffer);

    // Construct a cluster by deserializing.
    auto depgraph = ReadDepGraph<TestBitSet>(buffer);
    if (depgraph.TxCount() > 10) return;
    MakeConnected(depgraph);
    SanityCheck(depgraph);
    auto cluster = DepGraphToCluster(depgraph);

    // Construct a full linearizer for the cluster (which will reorder transactions).
    Linearizer lin(cluster);
    SanityCheck(lin.GetDepGraph());

    LIMITED_WHILE(!buffer.empty(), 100) {
        // Pick some subset of transactions of the cluster.
        TestBitSet todo = TestBitSet::Fill(cluster.size());
        uint64_t subset_int = ReadB128(buffer);
        for (unsigned i = 0; i < cluster.size(); ++i) {
            if ((subset_int >> i) & 1) todo.Reset(i);
        }
        // Find the best candidate subset of todo (interpreting todo as indices into the reordered list).
        auto best = lin.MapBack(lin.FindBestCandidate(todo, rng_seed));
        ++rng_seed;
        // Do the same using the naive dependency graph (first mapping todo back to the original order).
        auto real_best = FindBestCandidateNaive(depgraph, lin.MapBack(todo));
        // Compare them. The sets may differ, but they must have the same fee and size.
        assert(depgraph.FeeRate(best) == depgraph.FeeRate(real_best));
    }
}

FUZZ_TARGET(clusterlin_kernels)
{
    auto depgraph = ReadDepGraph<TestBitSet>(buffer);
    if (depgraph.TxCount() == 0 || depgraph.TxCount() > 10) return;
    MakeConnected(depgraph);
    SanityCheck(depgraph);

    const auto is_kernel = [&](const TestBitSet& kernel) {
        if (kernel.Count() <= 1) return false;
        if (kernel.Count() == depgraph.TxCount()) return false;
        if (depgraph.FindConnectedComponent(kernel) != kernel) return false;
        const auto anc = depgraph.Ancestors(kernel.First()) / kernel;
        const auto desc = depgraph.Descendants(kernel.First()) / kernel;
        for (auto tx : kernel) {
            if (depgraph.Ancestors(tx) / kernel != anc) return false;
            if (depgraph.Descendants(tx) / kernel != desc) return false;
        }

        return true;
    };

    auto kernels = FindKernels<TestBitSet>(depgraph);

    for (uint64_t x = 0; x >> depgraph.TxCount() == 0; ++x) {
        TestBitSet kernel;
        for (unsigned i = 0; i < depgraph.TxCount(); ++i) {
            kernel.Set(i, (x >> i) & 1);
        }
        bool real = is_kernel(kernel);
        bool seen = std::binary_search(kernels.begin(), kernels.end(), kernel);
        if (real != seen) {
            std::cerr << "GRAPH " << depgraph << "\n";
            std::cerr << "KERNEL " << kernel << "\n";
            std::cerr << "REAL " << real << "\n";
            std::cerr << "SEEN " << seen << "\n";
        }
        assert(real == seen);
    }
}
