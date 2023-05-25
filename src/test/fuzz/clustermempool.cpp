// Copyright (c) 2023 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <stdint.h>
#include <time.h>

#include <vector>

#include <cluster_linearize.h>
#include <test/fuzz/fuzz.h>
#include <test/fuzz/FuzzedDataProvider.h>
#include <test/fuzz/util.h>

#include <assert.h>

#include <iostream>

namespace {

/** Union-Find data structure. */
template<typename SizeType, SizeType Size>
class UnionFind
{
    SizeType m_ref[Size];
    SizeType m_size;

public:
    /** Initialize a UF data structure with size items, each in their own partition. */
    void Init(SizeType size)
    {
        m_size = size;
        for (SizeType i = 0; i < m_size; ++i) {
            m_ref[i] = i;
        }
    }

    /** Construct a UF data structure with size items, each in their own partition. */
    explicit UnionFind(SizeType size)
    {
        Init(size);
    }

    /** Find a representative of the partition that item idx is in. */
    SizeType Find(SizeType idx)
    {
        SizeType start = idx;
        // Chase references to make idx be the representative.
        while (m_ref[idx] != idx) {
            idx = m_ref[idx];
        }
        // Update all references along the way to point to idx.
        while (m_ref[start] != idx) {
            SizeType prev = start;
            start = m_ref[start];
            m_ref[prev] = idx;
        }
        return idx;
    }

    /** Merge the partitions that item a and item b are in. */
    void Union(SizeType a, SizeType b)
    {
        m_ref[Find(a)] = Find(b);
    }
};

template<typename I>
std::ostream& operator<<(std::ostream& s, const IntBitSet<I>& bs)
{
    s << "[";
    size_t cnt = 0;
    for (size_t i = 0; i < MAX_SIZE; ++i) {
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
std::ostream& operator<<(std::ostream& s, const MultiIntBitSet<I, N>& bs)
{
    s << "[";
    size_t cnt = 0;
    for (size_t i = 0; i < MAX_SIZE; ++i) {
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

/** Load a Cluster from fuzz provider. */
template<typename S>
Cluster<S> FuzzReadCluster(FuzzedDataProvider& provider, bool only_complete)
{
    Cluster<S> ret;
    while (ret.size() < S::MAX_SIZE && provider.remaining_bytes()) {
        if (only_complete && provider.remaining_bytes() < 4U + ret.size()) break;
        uint64_t sats = provider.ConsumeIntegralInRange<uint32_t>(0, 0xFFFF);
        uint32_t bytes = provider.ConsumeIntegralInRange<uint32_t>(1, 0x10000);
        S deps;
        for (size_t i = 0; i < ret.size(); ++i) {
            if (provider.ConsumeBool()) deps.Set(i);
        }
        ret.emplace_back(FeeAndSize{sats, bytes}, std::move(deps));
    }
    return ret;
}

/** Determine if select is a connected subset in the given cluster. */
template<typename S>
bool IsConnectedSubset(const Cluster<S>& cluster, const S& select)
{
    /* Trivial case. */
    if (select.None()) return true;

    /* Build up UF data structure. */
    UnionFind<unsigned, S::MAX_SIZE> uf(cluster.size());
    auto todo{select.Elements()};
    while (todo) {
        unsigned pos = todo.Next();
        auto deps{(cluster[pos].second & select).Elements()};
        while (deps) uf.Union(pos, deps.Next());
    }

    /* Test that all selected entries in uf have the same representative. */
    todo = select.Elements();
    unsigned root = uf.Find(todo.Next());
    while (todo) {
        if (uf.Find(todo.Next()) != root) return false;
    }
    return true;
}

/** A naive algorithm for finding the best candidate set.
 *
 * It constructs all 2^N subsets, tests if they satisfy dependency relations, and remembers the
 * best one out of those that do.
 */
template<typename S>
CandidateSetAnalysis<S> FindBestCandidateSetNaive(const Cluster<S>& cluster, const S& done)
{
    assert(cluster.size() <= 25); // This becomes really unwieldy for large clusters
    CandidateSetAnalysis<S> ret;

    // Iterate over all subsets of the cluster ((setval >> i) & 1 => tx i is included).
    for (uint32_t setval = 0; (setval >> cluster.size()) == 0; ++setval) {
        // Convert setval to a bitset, and also compute the merged ancestors of it in req.
        S bitset, req;
        for (unsigned i = 0; i < cluster.size(); ++i) {
            if ((setval >> i) & 1U) {
                bitset.Set(i);
                req = req | cluster[i].second;
            }
        }
        // None of the already done transactions may be included again.
        if ((done & bitset).Any()) continue;
        // We only consider non-empty additions.
        if (bitset.None()) continue;
        // All dependencies have to be satisfied.
        S unmet = req / (bitset | done);
        if (unmet.Any()) continue;
        // Only connected subsets are considered.
        if (!IsConnectedSubset(cluster, bitset)) continue;

        // Update statistics in ret to account for this new candidate.
        ++ret.num_candidate_sets;
        FeeAndSize feerate = ComputeSetFeeRate(cluster, bitset);
        if (ret.best_candidate_set.None() || FeeRateBetter(feerate, ret.best_candidate_feerate)) {
            ret.best_candidate_set = bitset;
            ret.best_candidate_feerate = feerate;
        }
    }

    return ret;
}

/** An O(2^n) algorithm for finding the best candidate set.
 *
 * It efficiently constructs all valid candidate sets, and remembers the best one.
 */
template<typename S>
CandidateSetAnalysis<S> FindBestCandidateSetExhaustive(const Cluster<S>& cluster, const AncestorSets<S>& anc, const S& done)
{
    // Queue of work units. Each consists of:
    // - inc: bitset of transactions definitely included (always includes done)
    // - exc: bitset of transactions definitely excluded
    // - feerate: the feerate of (included / done)
    std::vector<std::tuple<S, S, FeeAndSize>> queue;
    queue.emplace_back(done, S{}, FeeAndSize{});

    CandidateSetAnalysis<S> ret;

    // Process the queue.
    while (!queue.empty()) {
        ++ret.iterations;
        // Pop top element of the queue.
        auto [inc, exc, feerate] = queue.back();
        queue.pop_back();
        bool inc_none = inc == done;
        // Look for a transaction to include.
        for (size_t i = 0; i < cluster.size(); ++i) {
            // Conditions:
            // - !inc[i]: we can't add anything already included
            // - !exc[i]: we can't add anything already excluded
            // - (exc & anc[i]).None: ancestry of what we include cannot have excluded transactions
            // - inc_none || !((inc & anc[i]) / done).None(): either:
            //   - we're starting from an empty set (apart from done)
            //   - if not, the ancestry of what we add must overlap with what we already have, in
            //     not yet done transactions (to guarantee (inc / done) is always connected).
            if (!inc[i] && !exc[i] && (exc & anc[i]).None() && (inc_none || !((inc & anc[i]) / done).None())) {
                // First, add a queue item with i added to exc. Inc is unchanged, so feerate is
                // unchanged as well.
                auto new_exc = exc;
                new_exc.Set(i);
                queue.emplace_back(inc, new_exc, feerate);

                // Then, add a queue item with i (plus ancestry) added to inc. We need to compute
                // an updated feerate here to account for what was added.
                auto new_inc = inc | anc[i];
                FeeAndSize new_feerate = feerate + ComputeSetFeeRate(cluster, new_inc / inc);
                queue.emplace_back(new_inc, exc, new_feerate);

                // Update statistics in ret to account for this new candidate (new_inc / done).
                ++ret.num_candidate_sets;
                if (ret.best_candidate_set.None() || FeeRateBetter(new_feerate, ret.best_candidate_feerate)) {
                    ret.best_candidate_set = new_inc / done;
                    ret.best_candidate_feerate = new_feerate;
                }
                ret.max_queue_size = std::max(queue.size(), ret.max_queue_size);
                break;
            }
        }
    }

    return ret;
}

using BitSet = MultiIntBitSet<uint64_t, 2>;

} // namespace

FUZZ_TARGET(clustermempool_exhaustive_equals_naive)
{
    FuzzedDataProvider provider(buffer.data(), buffer.size());

    // Read cluster from fuzzer.
    Cluster<BitSet> cluster = FuzzReadCluster<BitSet>(provider, /*only_complete=*/true);
    // Compute ancestor sets.
    AncestorSets anc(cluster);
    // Find a topologically (but not necessarily connect) subset to set as "done" already.
    BitSet done;
    for (size_t i = 0; i < cluster.size(); ++i) {
        if (provider.ConsumeBool()) {
            done |= anc[i];
        }
    }

    // Run both algorithms.
    auto ret_naive = FindBestCandidateSetNaive(cluster, done);
    auto ret_exhaustive = FindBestCandidateSetExhaustive(cluster, anc, done);

    // Compute number of candidate sets and best feerate of found result.
    assert(ret_exhaustive.num_candidate_sets == ret_naive.num_candidate_sets);
    assert(ret_exhaustive.best_candidate_feerate == ret_naive.best_candidate_feerate);

    // We cannot require that the actual candidate returned is identical, because there may be
    // multiple, and the algorithms iterate in different order. Instead, recompute the feerate of
    // the candidate returned by the exhaustive one and check that it matches the claimed value.
    auto feerate_exhaustive = ComputeSetFeeRate(cluster, ret_exhaustive.best_candidate_set);
    assert(feerate_exhaustive == ret_exhaustive.best_candidate_feerate);
}

FUZZ_TARGET(clustermempool_efficient_equals_exhaustive)
{
    FuzzedDataProvider provider(buffer.data(), buffer.size());

    // Read cluster from fuzzer.
    Cluster<BitSet> cluster = FuzzReadCluster<BitSet>(provider, /*only_complete=*/true);
    // Compute ancestor sets.
    AncestorSets anc(cluster);

    // Find a topologically (but not necessarily connected) subset to set as "done" already.
    BitSet done;
    for (size_t i = 0; i < cluster.size(); ++i) {
        if (provider.ConsumeBool()) {
            done |= anc[i];
        }
    }

    // Sort the cluster by individual feerate.
    SortedCluster<BitSet> cluster_sorted(cluster);
    // Compute ancestor sets.
    AncestorSets<BitSet> anc_sorted(cluster_sorted.cluster);
    // Compute descendant sets.
    DescendantSets<BitSet> desc_sorted(anc_sorted);
    // Convert done to sorted ordering.
    BitSet done_sorted = cluster_sorted.OriginalToSorted(done);

    // Run both algorithms.
    auto ret_exhaustive = FindBestCandidateSetExhaustive(cluster, anc, done);
    auto ret_efficient = FindBestCandidateSetEfficient(cluster_sorted.cluster, anc_sorted, desc_sorted, done_sorted);

    // Compare best found feerates.
    assert(ret_exhaustive.best_candidate_feerate == ret_efficient.best_candidate_feerate);

    // We cannot require that the actual candidate returned is identical, because there may be
    // multiple, and the algorithms iterate in different order. Instead, recompute the feerate of
    // the candidate returned by the efficient one and check that it matches the claimed value.
    auto feerate_efficient = ComputeSetFeeRate(cluster_sorted.cluster, ret_efficient.best_candidate_set);
    assert(feerate_efficient == ret_exhaustive.best_candidate_feerate);
}

FUZZ_TARGET(clustermempool_linearize)
{
    FuzzedDataProvider provider(buffer.data(), buffer.size());

    Cluster<BitSet> cluster = FuzzReadCluster<BitSet>(provider, /*only_complete=*/false);

    BitSet all;
    for (unsigned i = 0; i < cluster.size(); ++i) all.Set(i);
    if (!IsConnectedSubset(cluster, all)) return;

    std::vector<std::pair<double, std::vector<unsigned>>> results;
    results.reserve(11);

    for (unsigned i = 0; i < 11; ++i) {
        struct timespec measure_start, measure_stop;
        clock_gettime(CLOCK_THREAD_CPUTIME_ID, &measure_start);
        auto linearization = LinearizeCluster(cluster);
        clock_gettime(CLOCK_THREAD_CPUTIME_ID, &measure_stop);
        double duration = (double)((int64_t)measure_stop.tv_sec - (int64_t)measure_start.tv_sec) + 0.000000001*(double)((int64_t)measure_stop.tv_nsec - (int64_t)measure_start.tv_nsec);
        results.emplace_back(duration, linearization);
    }

    std::sort(results.begin(), results.end(), [](const auto& a, const auto& b) { return a.first < b.first; });
    const auto& [duration, linearization] = results[5];

    BitSet satisfied;
    assert(linearization.size() == cluster.size());
    for (unsigned idx : linearization) {
        assert((cluster[idx].second / satisfied).None());
        satisfied.Set(idx);
    }
    assert(satisfied == all);

    std::cerr << "LINEARIZE(" << cluster.size() << ") time=" << duration /*<< " iters=" << stats.iterations << " time/iters=" << (duration / stats.iterations) << " comps=" << stats.comparisons << " time/comps=" << (duration / stats.comparisons)*/ << std::endl;
}
