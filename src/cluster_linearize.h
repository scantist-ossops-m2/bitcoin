// Copyright (c) 2023 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CLUSTER_LINEARIZE_H
#define BITCOIN_CLUSTER_LINEARIZE_H

#include <span.h>

#include <stdint.h>
#include <algorithm>
#include <limits>
#include <numeric>
#include <optional>
#include <vector>

#include <assert.h>

namespace cluster_linearize {

namespace {

/** Wrapper around __builtin_ctz* for supporting unsigned integer types. */
template<typename I>
unsigned inline CountTrailingZeroes(I v)
{
    static_assert(std::is_integral_v<I> && std::is_unsigned_v<I> && std::numeric_limits<I>::radix == 2);
    constexpr auto digits = std::numeric_limits<I>::digits;
    constexpr auto digits_u = std::numeric_limits<unsigned>::digits;
    constexpr auto digits_ul = std::numeric_limits<unsigned long>::digits;
    constexpr auto digits_ull = std::numeric_limits<unsigned long long>::digits;
    if constexpr (digits <= digits_u) {
        return __builtin_ctz(v);
    } else if constexpr (digits <= digits_ul) {
        return __builtin_ctzl(v);
    } else {
        static_assert(digits <= digits_ull);
        return __builtin_ctzll(v);
    }
}

/** Wrapper around __builtin_popcount* for supporting unsigned integer types. */
template<typename I>
unsigned inline PopCount(I v)
{
    static_assert(std::is_integral_v<I> && std::is_unsigned_v<I> && std::numeric_limits<I>::radix == 2);
    constexpr auto digits = std::numeric_limits<I>::digits;
    constexpr auto digits_u = std::numeric_limits<unsigned>::digits;
    constexpr auto digits_ul = std::numeric_limits<unsigned long>::digits;
    constexpr auto digits_ull = std::numeric_limits<unsigned long long>::digits;
    if constexpr (digits <= digits_u) {
        return __builtin_popcount(v);
    } else if constexpr (digits <= digits_ul) {
        return __builtin_popcountl(v);
    } else {
        static_assert(digits <= digits_ull);
        return __builtin_popcountll(v);
    }
}

/** Data structure storing a fee (in sats) and a size (in vbytes or weight units).
 *
 * The size of a FeeFrac cannot be zero unless the fee is also zero.
 *
 * FeeFracs have a total ordering, which first sorts by increasing feerate (fee/size), and then
 * uses decreasing size as tie-breaker. All standard comparison operators (==, !=, >, <, >=, <=)
 * respect this ordering. The >> and << operators only compare feerate and treat equal feerate but
 * different size as equivalent. These comparisons are only guaranteed to be correct when the
 * product of the highest fee and highest size does not exceed 2^64-1 (which allows up to 46116.86
 * BTC at size 4000000).
 */
struct FeeFrac
{
    /** Fee (in sats). */
    uint64_t fee;
    /** Size (in vbytes or weight units). */
    uint32_t size;

    /** Construct an IsEmpty() FeeFrac. */
    inline FeeFrac() noexcept : fee{0}, size{0} {}

    /** Construct a FeeFrac with specified fee and size. */
    inline FeeFrac(uint64_t s, uint32_t b) noexcept : fee{s}, size{b}
    {
        // If size==0, fee must be 0 as well.
        assert(size != 0 || fee == 0);
    }

    inline FeeFrac(const FeeFrac&) noexcept = default;
    inline FeeFrac& operator=(const FeeFrac&) noexcept = default;

    /** Check if this is empty (size, and implicitly fee, 0). */
    bool inline IsEmpty() const noexcept {
        return size == 0;
    }

    /** Add size and size of another FeeFrac to this one. */
    void inline operator+=(const FeeFrac& other) noexcept
    {
        fee += other.fee;
        size += other.size;
    }

    /** Subtrack size and size of another FeeFrac from this one. */
    void inline operator-=(const FeeFrac& other) noexcept
    {
        fee -= other.fee;
        size -= other.size;
        assert(size != 0 || fee == 0);
    }

    /** Sum fee and size. */
    friend inline FeeFrac operator+(const FeeFrac& a, const FeeFrac& b) noexcept
    {
        return {a.fee + b.fee, a.size + b.size};
    }

    /** Subtract both fee and size. */
    friend inline FeeFrac operator-(const FeeFrac& a, const FeeFrac& b) noexcept
    {
        return {a.fee - b.fee, a.size - b.size};
    }

    /** Check if two FeeFrac objects are equal (both same fee and same size). */
    friend inline bool operator==(const FeeFrac& a, const FeeFrac& b) noexcept
    {
        return a.fee == b.fee && a.size == b.size;
    }

    /** Check if two FeeFrac objects are different (not both same and same size). */
    friend inline bool operator!=(const FeeFrac& a, const FeeFrac& b) noexcept
    {
        return a.fee == b.fee && a.size == b.size;
    }

    /** Check if a FeeFrac object is worse than another. */
    friend inline bool operator<(const FeeFrac& a, const FeeFrac& b) noexcept
    {
        uint64_t a_val = a.fee * b.size;
        uint64_t b_val = b.fee * a.size;
        if (a_val != b_val) return a_val < b_val;
        return a.size > b.size;
    }

    /** Check if a FeeFrac object is worse or equal than another. */
    friend inline bool operator<=(const FeeFrac& a, const FeeFrac& b) noexcept
    {
        uint64_t a_val = a.fee * b.size;
        uint64_t b_val = b.fee * a.size;
        if (a_val != b_val) return a_val < b_val;
        return a.size >= b.size;
    }

    /** Check if a FeeFrac object is better than another. */
    friend inline bool operator>(const FeeFrac& a, const FeeFrac& b) noexcept
    {
        uint64_t a_val = a.fee * b.size;
        uint64_t b_val = b.fee * a.size;
        if (a_val != b_val) return a_val > b_val;
        return a.size < b.size;
    }

    /** Check if a FeeFrac object is better or equal than another. */
    friend inline bool operator>=(const FeeFrac& a, const FeeFrac& b) noexcept
    {
        uint64_t a_val = a.fee * b.size;
        uint64_t b_val = b.fee * a.size;
        if (a_val != b_val) return a_val > b_val;
        return a.size <= b.size;
    }

    /** Check if a FeeFrac object has strictly lower feerate than another. */
    friend inline bool operator<<(const FeeFrac& a, const FeeFrac& b) noexcept
    {
        return a.fee * b.size < b.fee * a.size;
    }

    /** Check if a FeeFrac object has strictly higher feerate than another. */
    friend inline bool operator>>(const FeeFrac& a, const FeeFrac& b) noexcept
    {
        return a.fee * b.size > b.fee * a.size;
    }
};

/** A bitset implementation backed by a single integer of type I. */
template<typename I>
class IntBitSet
{
    // Only binary, unsigned, integer, types allowed.
    static_assert(std::is_integral_v<I> && std::is_unsigned_v<I> && std::numeric_limits<I>::radix == 2);

    /** Integer whose bits represent this bitset. */
    I m_val;

    IntBitSet(I val) noexcept : m_val{val} {}

    /** Class of objects returned by Elements(). */
    class BitPopper
    {
        I m_val;
        friend class IntBitSet;
        BitPopper(I val) noexcept : m_val(val) {}
    public:
        explicit operator bool() const noexcept { return m_val != 0; }

        unsigned Next() noexcept
        {
            int ret = CountTrailingZeroes(m_val);
            m_val &= m_val - I{1U};
            return ret;
        }
    };

public:
    /** Number of elements this set type supports. */
    static constexpr unsigned MAX_SIZE = std::numeric_limits<I>::digits;

    /** Construct an empty set. */
    IntBitSet() noexcept : m_val{0} {}
    /** Copy a set. */
    IntBitSet(const IntBitSet&) noexcept = default;
    /** Copy-assign a set. */
    IntBitSet& operator=(const IntBitSet&) noexcept = default;

    /** Construct a set with elements 0..count-1. */
    static IntBitSet Full(unsigned count) noexcept {
        IntBitSet ret;
        if (count) ret.m_val = (~I{0}) >> (MAX_SIZE - count);
        return ret;
    }

    /** Compute the size of a set (number of elements). */
    unsigned Count() const noexcept { return PopCount(m_val); }
    /** Add an element to a set. */
    void Add(unsigned pos) noexcept { m_val |= I{1U} << pos; }
    /** Find if an element is in the set. */
    bool operator[](unsigned pos) const noexcept { return (m_val >> pos) & 1U; }
    /** Check if a set is empty. */
    bool IsEmpty() const noexcept { return m_val == 0; }
    /** Construct an object that will produce all elements of this set, using Next(). */
    BitPopper Elements() const noexcept { return BitPopper(m_val); }
    /** Find the first element (requires !IsEMpty()). */
    unsigned First() const noexcept { return CountTrailingZeroes(m_val); }
    /** Update this to be the union of this and a. */
    IntBitSet& operator|=(const IntBitSet& a) noexcept { m_val |= a.m_val; return *this; }
    /** Update this to be intersection of this and a. */
    IntBitSet& operator&=(const IntBitSet& a) noexcept { m_val &= a.m_val; return *this; }
    /** Construct a new set that is the interaction of a and b. */
    friend IntBitSet operator&(const IntBitSet& a, const IntBitSet& b) noexcept { return IntBitSet{a.m_val & b.m_val}; }
    /** Construct a new set that is the union of a and b. */
    friend IntBitSet operator|(const IntBitSet& a, const IntBitSet& b) noexcept { return IntBitSet{a.m_val | b.m_val}; }
    /** Construct a new set that is a minus b. */
    friend IntBitSet operator/(const IntBitSet& a, const IntBitSet& b) noexcept { return IntBitSet{a.m_val & ~b.m_val}; }
    /** Check if set a and set b are identical. */
    friend bool operator!=(const IntBitSet& a, const IntBitSet& b) noexcept { return a.m_val != b.m_val; }
    /** Check if set a and set b are different. */
    friend bool operator==(const IntBitSet& a, const IntBitSet& b) noexcept { return a.m_val == b.m_val; }
    /** Check if set a is a superset of set b. */
    friend bool operator>>(const IntBitSet& a, const IntBitSet& b) noexcept { return (b.m_val & ~a.m_val) == 0; }
};

/** A bitset implementation backed by N integers of type I. */
template<typename I, unsigned N>
class MultiIntBitSet
{
    // Only binary, unsigned, integer, types allowed.
    static_assert(std::is_integral_v<I> && std::is_unsigned_v<I> && std::numeric_limits<I>::radix == 2);
    static constexpr unsigned LIMB_BITS = std::numeric_limits<I>::digits;

    std::array<I, N> m_val;

    class BitPopper
    {
        std::array<I, N> m_val;
        mutable unsigned m_idx;
        friend class MultiIntBitSet;
        BitPopper(const std::array<I, N>& val) : m_val(val), m_idx{0} {}

    public:
        explicit operator bool() const noexcept
        {
            while (m_idx < N && m_val[m_idx] == 0) ++m_idx;
            return m_idx < N;
        }

        unsigned Next() noexcept
        {
            while (m_val[m_idx] == 0) ++m_idx;
            assert(m_idx < N);
            int ret = CountTrailingZeroes(m_val[m_idx]);
            m_val[m_idx] &= m_val[m_idx] - I{1U};
            return ret + m_idx * LIMB_BITS;
        }
    };

public:
    static constexpr unsigned MAX_SIZE = LIMB_BITS * N;

    MultiIntBitSet() noexcept : m_val{} {}
    MultiIntBitSet(const MultiIntBitSet&) noexcept = default;
    MultiIntBitSet& operator=(const MultiIntBitSet&) noexcept = default;

    void Add(unsigned pos) noexcept { m_val[pos / LIMB_BITS] |= I{1U} << (pos % LIMB_BITS); }
    bool operator[](unsigned pos) const noexcept { return (m_val[pos / LIMB_BITS] >> (pos % LIMB_BITS)) & 1U; }

    static MultiIntBitSet Full(unsigned count) noexcept {
        MultiIntBitSet ret;
        if (count) {
            unsigned i = 0;
            while (count > LIMB_BITS) {
                ret.m_val[i++] = ~I{0};
                count -= LIMB_BITS;
            }
            ret.m_val[i] = (~I{0}) >> (LIMB_BITS - count);
        }
        return ret;
    }

    unsigned Count() const noexcept
    {
        unsigned ret{0};
        for (I v : m_val) ret += PopCount(v);
        return ret;
    }

    bool IsEmpty() const noexcept
    {
        for (auto v : m_val) {
            if (v != 0) return false;
        }
        return true;
    }

    BitPopper Elements() const noexcept { return BitPopper(m_val); }

    unsigned First() const noexcept
    {
        unsigned p = 0;
        while (m_val[p] == 0) ++p;
        return CountTrailingZeroes(m_val[p]) + p * LIMB_BITS;
    }

    MultiIntBitSet& operator|=(const MultiIntBitSet& a) noexcept
    {
        for (unsigned i = 0; i < N; ++i) {
            m_val[i] |= a.m_val[i];
        }
        return *this;
    }

    MultiIntBitSet& operator&=(const MultiIntBitSet& a) noexcept
    {
        for (unsigned i = 0; i < N; ++i) {
            m_val[i] &= a.m_val[i];
        }
        return *this;
    }

    friend MultiIntBitSet operator&(const MultiIntBitSet& a, const MultiIntBitSet& b) noexcept
    {
        MultiIntBitSet r;
        for (unsigned i = 0; i < N; ++i) {
            r.m_val[i] = a.m_val[i] & b.m_val[i];
        }
        return r;
    }

    friend MultiIntBitSet operator|(const MultiIntBitSet& a, const MultiIntBitSet& b) noexcept
    {
        MultiIntBitSet r;
        for (unsigned i = 0; i < N; ++i) {
            r.m_val[i] = a.m_val[i] | b.m_val[i];
        }
        return r;
    }

    friend MultiIntBitSet operator/(const MultiIntBitSet& a, const MultiIntBitSet& b) noexcept
    {
        MultiIntBitSet r;
        for (unsigned i = 0; i < N; ++i) {
            r.m_val[i] = a.m_val[i] & ~b.m_val[i];
        }
        return r;
    }

    friend bool operator>>(const MultiIntBitSet& a, const MultiIntBitSet& b) noexcept
    {
        for (unsigned i = 0; i < N; ++i) {
            if (b.m_val[i] & ~a.m_val[i]) return false;
        }
        return true;
    }

    friend bool operator!=(const MultiIntBitSet& a, const MultiIntBitSet& b) noexcept { return a.m_val != b.m_val; }
    friend bool operator==(const MultiIntBitSet& a, const MultiIntBitSet& b) noexcept { return a.m_val == b.m_val; }
};

/** Data type to represent cluster input.
 *
 * cluster[i].first is tx_i's fee and size.
 * cluster[i].second[j] is true iff tx_i spends one or more of tx_j's outputs.
 */
template<typename S>
using Cluster = std::vector<std::pair<FeeFrac, S>>;

/** Precomputation data structure with all ancestor sets of a cluster. */
template<typename S>
class AncestorSets
{
    std::vector<S> m_ancestorsets;

public:
    explicit AncestorSets(const Cluster<S>& cluster)
    {
        // Initialize: every transaction's ancestor set is itself plus direct parents.
        m_ancestorsets.resize(cluster.size());
        for (size_t i = 0; i < cluster.size(); ++i) {
            m_ancestorsets[i] = cluster[i].second;
            m_ancestorsets[i].Add(i);
        }

        // Propagate
        for (unsigned i = 0; i < cluster.size(); ++i) {
            // At this point, m_ancestorsets[a][b] is true iff b is an ancestor of a and there is
            // a path from a to b through the subgraph consisting of {a, b} union {0..(i-1)}.
            S to_merge = m_ancestorsets[i];
            for (unsigned j = 0; j < cluster.size(); ++j) {
                if (m_ancestorsets[j][i]) {
                    m_ancestorsets[j] |= to_merge;
                }
            }
        }
    }

    AncestorSets() noexcept = default;
    AncestorSets(const AncestorSets&) = delete;
    AncestorSets(AncestorSets&&) noexcept = default;
    AncestorSets& operator=(const AncestorSets&) = delete;
    AncestorSets& operator=(AncestorSets&&) noexcept = default;

    const S& operator[](unsigned pos) const noexcept { return m_ancestorsets[pos]; }
    size_t Size() const noexcept { return m_ancestorsets.size(); }
};
/** Precomputation data structure with all descendant sets of a cluster. */
template<typename S>
class DescendantSets
{
    std::vector<S> m_descendantsets;

public:
    explicit DescendantSets(const AncestorSets<S>& anc)
    {
        m_descendantsets.resize(anc.Size());
        for (size_t i = 0; i < anc.Size(); ++i) {
            auto ancestors{anc[i].Elements()};
            while (ancestors) {
                m_descendantsets[ancestors.Next()].Add(i);
            }
        }
    }

    DescendantSets() noexcept = default;
    DescendantSets(const DescendantSets&) = delete;
    DescendantSets(DescendantSets&&) noexcept = default;
    DescendantSets& operator=(const DescendantSets&) = delete;
    DescendantSets& operator=(DescendantSets&&) noexcept = default;

    const S& operator[](unsigned pos) const noexcept { return m_descendantsets[pos]; }
};

/** Output of FindBestCandidateSet* functions. */
template<typename S>
struct CandidateSetAnalysis
{
    /** Total number of candidate sets found/considered. */
    size_t num_candidate_sets{0};
    /** Best found candidate set. */
    S best_candidate_set{};
    /** Fee and size of best found candidate set. */
    FeeFrac best_candidate_feefrac{};
    /** Index of the chosen transaction (ancestor set algorithm only). */
    unsigned chosen_transaction{0};

    /** Maximum search queue size. */
    size_t max_queue_size{0};
    /** Total number of queue processing iterations performed. */
    size_t iterations{0};
    /** Number of feefrac comparisons performed. */
    size_t comparisons{0};
};

/** Compute the combined fee and size of a subset of a cluster. */
template<typename S>
FeeFrac ComputeSetFeeFrac(const Cluster<S>& cluster, const S& select)
{
    FeeFrac ret;
    auto todo{select.Elements()};
    while (todo) {
        ret += cluster[todo.Next()].first;
    }
    return ret;
}

/** Precomputed ancestor FeeFracs. */
template<typename S>
class AncestorSetFeeFracs
{
    std::vector<FeeFrac> m_anc_feefracs;

public:
    /** Construct a precomputed AncestorSetFeeFracs object for given cluster/done. */
    explicit AncestorSetFeeFracs(const Cluster<S>& cluster, const AncestorSets<S>& anc, const S& done) noexcept
    {
        m_anc_feefracs.resize(cluster.size());
        for (unsigned i = 0; i < cluster.size(); ++i) {
            if (!done[i]) {
                m_anc_feefracs[i] = ComputeSetFeeFrac(cluster, anc[i] / done);
            }
        }
    }

    /** Update the precomputed data structure to reflect that new_done was added to done. */
    void Done(const Cluster<S>& cluster, const DescendantSets<S>& desc, const S& new_done) noexcept
    {
        auto todo{new_done.Elements()};
        while (todo) {
            unsigned pos = todo.Next();
            FeeFrac feefrac = cluster[pos].first;
            auto todo_desc{(desc[pos] / new_done).Elements()};
            while (todo_desc) {
                m_anc_feefracs[todo_desc.Next()] -= feefrac;
            }
        }
    }

    const FeeFrac& operator[](unsigned i) const noexcept { return m_anc_feefracs[i]; }
};

/** Precomputation data structure for sorting a cluster based on individual transaction FeeFrac. */
template<typename S>
struct SortedCluster
{
    /** The cluster in individual FeeFrac sorted order (both itself and its dependencies) */
    Cluster<S> cluster;
    /** Mapping from the original order (input to constructor) to sorted order. */
    std::vector<unsigned> original_to_sorted;
    /** Mapping back from sorted order to the order given to the constructor. */
    std::vector<unsigned> sorted_to_original;

    /** Given a set with indexes in original order, compute one in sorted order. */
    S OriginalToSorted(const S& val) const noexcept
    {
        S ret;
        auto todo{val.Elements()};
        while (todo) {
            ret.Add(original_to_sorted[todo.Next()]);
        }
        return ret;
    }

    /** Given a set with indexes in sorted order, compute on in original order. */
    S SortedToOriginal(const S& val) const noexcept
    {
        S ret;
        auto todo{val.Elements()};
        while (todo) {
            ret.Add(sorted_to_original[todo.Next()]);
        }
        return ret;
    }

    /** Construct a sorted cluster object given a (non-sorted) cluster as input. */
    SortedCluster(const Cluster<S>& orig_cluster)
    {
        // Allocate vectors.
        sorted_to_original.resize(orig_cluster.size());
        original_to_sorted.resize(orig_cluster.size());
        cluster.resize(orig_cluster.size());
        // Compute sorted_to_original mapping.
        std::iota(sorted_to_original.begin(), sorted_to_original.end(), 0U);
        std::sort(sorted_to_original.begin(), sorted_to_original.end(), [&](unsigned i, unsigned j) {
            if (orig_cluster[i].first == orig_cluster[j].first) {
                return i < j;
            }
            return orig_cluster[i].first > orig_cluster[j].first;
        });
        // Use sorted_to_original to fill original_to_sorted.
        for (size_t i = 0; i < orig_cluster.size(); ++i) {
            original_to_sorted[sorted_to_original[i]] = i;
        }
        // Use sorted_to_original to fill cluster.
        for (size_t i = 0; i < orig_cluster.size(); ++i) {
            cluster[i].first = orig_cluster[sorted_to_original[i]].first;
            cluster[i].second = OriginalToSorted(orig_cluster[sorted_to_original[i]].second);
        }
    }
};

/** Given a cluster and its ancestor sets, find the one with the best FeeFrac. */
template<typename S>
CandidateSetAnalysis<S> FindBestAncestorSet(const Cluster<S>& cluster, const AncestorSets<S>& anc, const AncestorSetFeeFracs<S>& anc_feefracs, const S& done)
{
    CandidateSetAnalysis<S> ret;
    ret.max_queue_size = 1;

    for (size_t i = 0; i < cluster.size(); ++i) {
        if (done[i]) continue;
        ++ret.iterations;
        ++ret.num_candidate_sets;
        const FeeFrac& feefrac = anc_feefracs[i];
        assert(!feefrac.IsEmpty());
        bool new_best = ret.best_candidate_feefrac.IsEmpty();
        if (!new_best) {
            ++ret.comparisons;
            new_best = feefrac > ret.best_candidate_feefrac;
        }
        if (new_best) {
            ret.best_candidate_feefrac = feefrac;
            ret.best_candidate_set = anc[i] / done;
            ret.chosen_transaction = i;
        }
    }

    return ret;
}

enum class QueueStyle {
    DFS,
    DFS_EXC,
    RANDOM,
    MOST_ADVANCED_BEST_POTENTIAL_FEEFRAC,
    LEAST_ADVANCED_BEST_POTENTIAL_FEEFRAC,
    MOST_LEFT_BEST_POTENTIAL_FEEFRAC,
    LEAST_LEFT_BEST_POTENTIAL_FEEFRAC,
    MOST_INC_BEST_POTENTIAL_FEEFRAC,
    LEAST_INC_BEST_POTENTIAL_FEEFRAC,
    BEST_ACHIEVED_FEEFRAC,
    HIGHEST_ACHIEVED_FEE,
    HIGHEST_ACHIEVED_SIZE,
    BEST_POTENTIAL_FEEFRAC,
    HIGHEST_POTENTIAL_FEE,
    HIGHEST_POTENTIAL_SIZE,
    BEST_GAIN_FEEFRAC,
    HIGHEST_GAIN_FEE,
    HIGHEST_GAIN_SIZE,
    WORST_ACHIEVED_FEEFRAC,
    LOWEST_ACHIEVED_FEE,
    LOWEST_ACHIEVED_SIZE,
    WORST_POTENTIAL_FEEFRAC,
    LOWEST_POTENTIAL_FEE,
    LOWEST_POTENTIAL_SIZE,
    WORST_GAIN_FEEFRAC,
    LOWEST_GAIN_FEE,
    LOWEST_GAIN_SIZE,
};

/** An efficient algorithm for finding the best candidate set. Believed to be O(~1.6^n).
 *
 * cluster must be sorted (see SortedCluster) by individual feerate, and anc/desc/done must use
 * the same indexing as cluster.
 */
template<QueueStyle QS, typename S, typename RNG>
CandidateSetAnalysis<S> FindBestCandidateSetEfficient(const Cluster<S>& cluster, const AncestorSets<S>& anc, const DescendantSets<S>& desc, const AncestorSetFeeFracs<S>& anc_feefracs, const S& done, RNG&& rng)
{
    // Queue of work units. Each consists of:
    // - inc: bitset of transactions definitely included (always includes done)
    // - exc: bitset of transactions definitely excluded
    // - pot: bitset of the best-FeeFrac subset of transactions including inc and excluding exc
    //        (ignoring topology).
    // - inc_feefrac: the FeeFrac of (included / done)
    // - pot_feefrac: the FeeFrac of (pot / done)
    using QueueElem = std::tuple<S, S, S, FeeFrac, FeeFrac>;
    std::vector<QueueElem> queue;

    CandidateSetAnalysis<S> ret;

    // Compute "all" set, with all the cluster's transaction.
    S all = S::Full(cluster.size());
    if (done == all) return ret;

    auto queue_cmp_fn = [&](const QueueElem& a, const QueueElem& b) {
        if constexpr (QS == QueueStyle::BEST_ACHIEVED_FEEFRAC) {
            return std::get<3>(b) > std::get<3>(a);
        } else if constexpr (QS == QueueStyle::HIGHEST_ACHIEVED_FEE) {
            return std::get<3>(b).fee > std::get<3>(a).fee;
        } else if constexpr (QS == QueueStyle::HIGHEST_ACHIEVED_SIZE) {
            return std::get<3>(b).size > std::get<3>(a).size;
        } else if constexpr (QS == QueueStyle::BEST_POTENTIAL_FEEFRAC) {
            return std::get<4>(b) > std::get<4>(a);
        } else if constexpr (QS == QueueStyle::HIGHEST_POTENTIAL_FEE) {
            return std::get<4>(b).fee > std::get<4>(a).fee;
        } else if constexpr (QS == QueueStyle::HIGHEST_POTENTIAL_SIZE) {
            return std::get<4>(b).size > std::get<4>(a).size;
        } else if constexpr (QS == QueueStyle::BEST_GAIN_FEEFRAC) {
            auto gain_a = std::get<4>(a) - std::get<3>(a);
            auto gain_b = std::get<4>(b) - std::get<3>(b);
            return gain_b > gain_a;
        } else if constexpr (QS == QueueStyle::HIGHEST_GAIN_FEE) {
            return std::get<4>(b).fee + std::get<3>(a).fee > std::get<4>(a).fee + std::get<3>(b).fee;
        } else if constexpr (QS == QueueStyle::HIGHEST_GAIN_SIZE) {
            return std::get<4>(b).size + std::get<3>(a).size > std::get<4>(a).size + std::get<3>(b).size;
        } else if constexpr (QS == QueueStyle::WORST_ACHIEVED_FEEFRAC) {
            return std::get<3>(a) > std::get<3>(b);
        } else if constexpr (QS == QueueStyle::LOWEST_ACHIEVED_FEE) {
            return std::get<3>(a).fee > std::get<3>(b).fee;
        } else if constexpr (QS == QueueStyle::LOWEST_ACHIEVED_SIZE) {
            return std::get<3>(a).size > std::get<3>(b).size;
        } else if constexpr (QS == QueueStyle::WORST_POTENTIAL_FEEFRAC) {
            return std::get<4>(a) > std::get<4>(b);
        } else if constexpr (QS == QueueStyle::LOWEST_POTENTIAL_FEE) {
            return std::get<4>(a).fee > std::get<4>(b).fee;
        } else if constexpr (QS == QueueStyle::LOWEST_POTENTIAL_SIZE) {
            return std::get<4>(a).size > std::get<4>(b).size;
        } else if constexpr (QS == QueueStyle::WORST_GAIN_FEEFRAC) {
            auto gain_a = std::get<4>(a) - std::get<3>(a);
            auto gain_b = std::get<4>(b) - std::get<3>(b);
            return gain_a > gain_b;
        } else if constexpr (QS == QueueStyle::LOWEST_GAIN_FEE) {
            return std::get<4>(a).fee + std::get<3>(b).fee > std::get<4>(b).fee + std::get<3>(a).fee;
        } else if constexpr (QS == QueueStyle::LOWEST_GAIN_SIZE) {
            return std::get<4>(a).size + std::get<3>(b).size > std::get<4>(b).size + std::get<3>(a).size;
        } else if constexpr (QS == QueueStyle::MOST_ADVANCED_BEST_POTENTIAL_FEEFRAC) {
            unsigned adv_a = (all / (std::get<0>(a) | std::get<1>(a))).First();
            unsigned adv_b = (all / (std::get<0>(b) | std::get<1>(b))).First();
            if (adv_a != adv_b) return adv_a < adv_b;
            return std::get<4>(b) > std::get<4>(a);
        } else if constexpr (QS == QueueStyle::LEAST_ADVANCED_BEST_POTENTIAL_FEEFRAC) {
            unsigned adv_a = (all / (std::get<0>(a) | std::get<1>(a))).First();
            unsigned adv_b = (all / (std::get<0>(b) | std::get<1>(b))).First();
            if (adv_a != adv_b) return adv_a > adv_b;
            return std::get<4>(b) > std::get<4>(a);
        } else if constexpr (QS == QueueStyle::MOST_LEFT_BEST_POTENTIAL_FEEFRAC) {
            unsigned left_a = (all / (std::get<0>(a) | std::get<1>(a))).Count();
            unsigned left_b = (all / (std::get<0>(b) | std::get<1>(b))).Count();
            if (left_a != left_b) return left_a < left_b;
            return std::get<4>(b) > std::get<4>(a);
        } else if constexpr (QS == QueueStyle::LEAST_LEFT_BEST_POTENTIAL_FEEFRAC) {
            unsigned left_a = (all / (std::get<0>(a) | std::get<1>(a))).Count();
            unsigned left_b = (all / (std::get<0>(b) | std::get<1>(b))).Count();
            if (left_a != left_b) return left_a > left_b;
            return std::get<4>(b) > std::get<4>(a);
        } else if constexpr (QS == QueueStyle::MOST_INC_BEST_POTENTIAL_FEEFRAC) {
            unsigned inc_a = std::get<0>(a).Count();
            unsigned inc_b = std::get<0>(b).Count();
            if (inc_a != inc_b) return inc_a < inc_b;
            return std::get<4>(b) > std::get<4>(a);
        } else if constexpr (QS == QueueStyle::LEAST_INC_BEST_POTENTIAL_FEEFRAC) {
            unsigned inc_a = std::get<0>(a).Count();
            unsigned inc_b = std::get<0>(b).Count();
            if (inc_a != inc_b) return inc_a > inc_b;
            return std::get<4>(b) > std::get<4>(a);
        } else {
            return false;
        }
    };

    S best_candidate;
    FeeFrac best_feefrac;

    // Internal add function. Arguments:
    // - inc: new included set of transactions
    // - exc: new excluded set of transactions
    // - inc_feefrac: feerate of (inc / done)
    // - inc_may_be_best: whether inc_feerate could be better than best_feerate
    // - pot_known: pointer to the pot of the new item, if known, nullptr otherwise.
    // - try_shrink: add unreachable subgraphs to exc
    auto add_fn = [&](S inc, S exc, FeeFrac inc_feefrac, bool inc_may_be_best, const S* pot_known, bool try_shrink) -> bool {
        if (try_shrink) {
            assert(pot_known == nullptr);
            S reach;
            reach.Add((inc / done).First());
            auto added = reach;
            while (true) {
                S new_reach = reach;
                auto reach_todo{added.Elements()};
                while (reach_todo) {
                    unsigned reach_pos = reach_todo.Next();
                    new_reach |= (anc[reach_pos] | desc[reach_pos]) / (exc | done);
                }
                if (reach == new_reach) break;
                added = new_reach / reach;
                reach = new_reach;
            }
            if ((done | reach) >> inc) {
                auto new_exc = all / (reach | done);
                assert(new_exc >> exc);
                exc = new_exc;
            } else {
                return false;
            }
        }

        // In the loop below, we do two things simultaneously:
        // - compute the pot_feefrac for the new queue item.
        // - perform "jump ahead", which may add additional transactions to inc
        /** The new potential feefrac. */
        FeeFrac pot_feefrac = inc_feefrac;
        /** The set of transactions corresponding to that potential feefrac. */
        S pot = inc;
        /** The set of ancestors of everything in pot, combined. */
        S pot_ancestors;
        /** Whether any undecided transactions with higher individual feefrac than inc_feefrac are left. */
        bool explore_further{false};
        if (pot_known == nullptr) {
            // Loop over all undecided transactions (not yet included or excluded), from good to bad feefrac.
            auto undecided{(all / (inc | exc)).Elements()};
            while (undecided) {
                unsigned pos = undecided.Next();
                // Determine if adding transaction pos to pot (ignoring topology) would improve it. If not,
                // we're done updating pot+pot_feefrac (and inc+inc_feefrac).
                if (!pot_feefrac.IsEmpty()) {
                    ++ret.comparisons;
                    if (!(cluster[pos].first >> pot_feefrac)) break;
                }
                // Add the transaction to pot+pot_feefrac.
                pot_feefrac += cluster[pos].first;
                pot.Add(pos);
                // Update the combined ancestors of pot.
                pot_ancestors |= anc[pos];
                // If at this point pot covers all its own ancestors, it means pot is topologically
                // valid. Perform jump ahead (update inc+inc_frac to match pot+pot_feefrac).
                if (pot >> pot_ancestors) {
                    inc = pot;
                    inc_feefrac = pot_feefrac;
                    inc_may_be_best = true;
                    explore_further = false;
                } else {
                    explore_further = true;
                }
            }
        } else {
            // In case we know the new work item's pot ialready, use a simplified loop which skips
            // the feefrac comparisons, and runs until pot_known is hit.
            auto todo{(*pot_known / inc).Elements()};
            while (todo) {
                unsigned pos = todo.Next();
                pot_feefrac += cluster[pos].first;
                pot.Add(pos);
                pot_ancestors |= anc[pos];
                if (pot >> pot_ancestors) {
                    inc = pot;
                    inc_feefrac = pot_feefrac;
                    inc_may_be_best = true;
                    explore_further = false;
                } else {
                    explore_further = true;
                }
            }
        }
        // If the potential feefrac is nothing, this is certainly uninteresting to work on.
        if (pot_feefrac.IsEmpty()) return false;

        // If inc is different from inc of the parent work item that spawned it, consider whether
        // it's the new best we've seen.
        if (inc_may_be_best) {
            ++ret.num_candidate_sets;
            assert(!inc_feefrac.IsEmpty());
            bool new_best = best_feefrac.IsEmpty();
            if (!new_best) {
                ++ret.comparisons;
                new_best = inc_feefrac > best_feefrac;
            }
            if (new_best) {
                best_feefrac = inc_feefrac;
                best_candidate = inc;
            }
        }

        // Only if any transactions with feefrac better than inc_feefrac exist add this entry to the
        // queue. If not, it's not worth exploring further.
        if (!explore_further) return false;

        queue.emplace_back(inc, exc, pot, inc_feefrac, pot_feefrac);
        ret.max_queue_size = std::max(ret.max_queue_size, queue.size());
        if constexpr (QS != QueueStyle::RANDOM && QS != QueueStyle::DFS && QS != QueueStyle::DFS_EXC) {
            std::push_heap(queue.begin(), queue.end(), queue_cmp_fn);
        }
        return true;
    };

    // Find best ancestor set to seed the search. Add a queue item corresponding to the transaction
    // with the best ancestor set feefrac excluded, and one with it included.
    auto ret_ancestor = FindBestAncestorSet(cluster, anc, anc_feefracs, done);
    add_fn(done, desc[ret_ancestor.chosen_transaction], {}, false, nullptr, false);
    add_fn(done | ret_ancestor.best_candidate_set, {}, ret_ancestor.best_candidate_feefrac, true, nullptr, true);

    // Work processing loop.
    while (queue.size()) {
        ++ret.iterations;

        if constexpr (QS == QueueStyle::RANDOM) {
            unsigned pos = ((rng() & 0xffffffff) * queue.size()) >> 32;
            if (pos + 1 != queue.size()) {
                std::swap(queue[pos], queue.back());
            }
        } else if constexpr (QS != QueueStyle::DFS && QS != QueueStyle::DFS_EXC) {
            std::pop_heap(queue.begin(), queue.end(), queue_cmp_fn);
        }

        // Pop the last element of the queue.
        auto [inc, exc, pot, inc_feefrac, pot_feefrac] = queue.back();
        queue.pop_back();

        // If this item's potential feefrac is not better than the best seen so far, drop it.
        assert(pot_feefrac.size > 0);
        if (!best_feefrac.IsEmpty()) {
            ++ret.comparisons;
            if (pot_feefrac <= best_feefrac) continue;
        }

        // Decide which transaction to split on (highest undecided individual feefrac one left).
        // There must be at least one such transaction, because otherwise explore_further would
        // have been false inside add_fn, and the entry would never have been added to the queue.
        auto pos = (all / (inc | exc)).First();

        // Consider adding a work item corresponding to that transaction excluded. As nothing is
        // being added to inc, this new entry cannot be a new best. As desc[pos] always overlaps
        // with pot (in pos, at least), the new work item's potential set will definitely be
        // different from the parent.
        bool added_exc = add_fn(inc, exc | desc[pos], inc_feefrac, false, nullptr, inc != done);

        // Consider adding a work item corresponding to that transaction included. Since only
        // connected subgraphs can be optimal candidates, if there is no overlap between the
        // parent's included transactions (inc) and the ancestors of the newly added transaction
        // (outside of done), we know it cannot possibly be the new best.
        // One exception to this is the first addition after an empty inc (inc=done). However,
        // due to the preseeding with the best ancestor set, we know that anything better must
        // necessarily consist of the union of at least two ancestor sets, and this is not a
        // concern.
        // In case anc[pos] is a subset of pot, the child potential will be identical to that of
        // the parent.
        auto new_inc = inc | anc[pos];
        auto new_inc_feefrac = inc_feefrac + ComputeSetFeeFrac(cluster, new_inc / inc);
        bool may_be_new_best = !(done >> (inc & anc[pos]));
        bool added_inc = add_fn(new_inc, exc, new_inc_feefrac, may_be_new_best, pot >> anc[pos] ? &pot : nullptr, inc == done);

        if constexpr (QS == QueueStyle::DFS_EXC) {
            if (added_inc && added_exc) {
                assert(queue.size() >= 2);
                std::swap(queue.back(), *std::next(queue.rbegin()));
            }
        }
    }

    // Return.
    ret.best_candidate_set = best_candidate / done;
    ret.best_candidate_feefrac = best_feefrac;
    return ret;
}

/** Compute a full linearization of a cluster (vector of cluster indices). */
template<typename S>
std::vector<unsigned> LinearizeCluster(const Cluster<S>& cluster, unsigned optimal_limit)
{
    std::vector<unsigned> ret;
    ret.reserve(cluster.size());
    S done;
    unsigned left = cluster.size();

    // Precompute stuff.
    SortedCluster<S> sorted(cluster);
    AncestorSets<S> anc(sorted.cluster);
    DescendantSets<S> desc(anc);
    // Precompute ancestor set sizes, to help with topological sort.
    std::vector<unsigned> anccount(cluster.size(), 0);
    for (unsigned i = 0; i < cluster.size(); ++i) {
        anccount[i] = anc[i].Count();
    }
    AncestorSetFeeFracs anc_feefracs(sorted.cluster, anc, done);

    // Iterate while there are transactions left.
    while (left > 0) {
        // Invoke function to find a good/best candidate.
        CandidateSetAnalysis<S> analysis;
        if (left > optimal_limit) {
            analysis = FindBestAncestorSet(sorted.cluster, anc, anc_feefracs, done);
        } else {
            analysis = FindBestCandidateSetEfficient<QueueStyle::LOWEST_POTENTIAL_SIZE>(sorted.cluster, anc, desc, anc_feefracs, done, nullptr);
        }

        // Sanity checks.
        assert(!analysis.best_candidate_set.IsEmpty()); // Must be at least one transaction
        assert((analysis.best_candidate_set & done).IsEmpty()); // Cannot overlap with processed ones.

        // Append candidate's transactions to linearization, and topologically sort them.
        size_t old_size = ret.size();
        auto to_set{analysis.best_candidate_set.Elements()};
        while (to_set) {
            ret.emplace_back(to_set.Next());
        }
        std::sort(ret.begin() + old_size, ret.end(), [&](unsigned a, unsigned b) {
            if (anccount[a] == anccount[b]) return a < b;
            return anccount[a] < anccount[b];
        });

        // Update bookkeeping to reflect newly added transactions.
        left -= analysis.best_candidate_set.Count();
        if (!left) break; // Bail out quickly if nothing left.
        done |= analysis.best_candidate_set;
        // Update precomputed ancestor FeeFracs.
        anc_feefracs.Done(sorted.cluster, desc, analysis.best_candidate_set);
#if 0
        // Verify that precomputed ancestor FeeFrac are correct.
        for (unsigned i = 0; i < cluster.size(); ++i) {
            if (!done[i]) {
                assert(anc_feefracs[i] == ComputeSetFeeFrac(sorted.cluster, anc[i] / done));
            }
        }
#endif
    }

    // Map linearization back from sorted cluster indices to original indices.
    for (unsigned i = 0; i < cluster.size(); ++i) {
        ret[i] = sorted.sorted_to_original[ret[i]];
    }

    return ret;
}

uint8_t ReadSpanByte(Span<const unsigned char>& data)
{
    if (data.empty()) return 0;
    uint8_t val = data[0];
    data = data.subspan(1);
    return val;
}

/** Deserialize a number, in little-endian 7 bit format, top bit set = more size. */
uint64_t DeserializeNumberBase128(Span<const unsigned char>& data)
{
    uint64_t ret{0};
    for (int i = 0; i < 10; ++i) {
        uint8_t b = ReadSpanByte(data);
        ret |= ((uint64_t)(b & uint8_t{0x7F})) << (7 * i);
        if ((b & 0x80) == 0) break;
    }
    return ret;
}

/** Serialize a number, in little-endian 7 bit format, top bit set = more size. */
void SerializeNumberBase128(uint64_t val, std::vector<unsigned char>& data)
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

/** Serialize a cluster in the following format:
 *
 * - For every transaction:
 *   - Base128 encoding of its byte size (at least 1, max 2^22-1).
 *   - Base128 encoding of its fee in fee (max 2^51-1).
 *   - For each of its direct parents:
 *     - If parent_idx < child_idx:
 *       - Base128 encoding of (child_idx - parent_idx)
 *     - If parent_idx > child_idx:
 *       - Base128 encoding of (parent_idx)
 *   - A zero byte
 * - A zero byte
 */
template<typename S>
void SerializeCluster(const Cluster<S>& cluster, std::vector<unsigned char>& data)
{
    for (unsigned i = 0; i < cluster.size(); ++i) {
        SerializeNumberBase128(cluster[i].first.size, data);
        SerializeNumberBase128(cluster[i].first.fee, data);
        for (unsigned j = 1; j <= i; ++j) {
            if (cluster[i].second[i - j]) SerializeNumberBase128(j, data);
        }
        for (unsigned j = i + 1; j < cluster.size(); ++j) {
            if (cluster[i].second[j]) SerializeNumberBase128(j, data);
        }
        data.push_back(0);
    }
    data.push_back(0);
}

/** Deserialize a cluster in the same format as SerializeCluster (overflows wrap). */
template<typename S>
Cluster<S> DeserializeCluster(Span<const unsigned char>& data)
{
    Cluster<S> ret;
    while (ret.size() < S::MAX_SIZE) {
        uint32_t size = DeserializeNumberBase128(data) & 0x3fffff;
        if (size == 0) break;
        uint64_t fee = DeserializeNumberBase128(data) & 0x7ffffffffffff;
        S parents;
        while (true) {
            unsigned read = DeserializeNumberBase128(data);
            if (read == 0) break;
            if (read <= ret.size()) {
                parents.Add(ret.size() - read);
            } else {
                if (read < S::MAX_SIZE) parents.Add(read);
            }
        }
        ret.emplace_back(FeeFrac{fee, size}, std::move(parents));
    }
    S all = S::Full(ret.size());
    for (unsigned i = 0; i < ret.size(); ++i) {
        ret[i].second &= all;
    }
    return ret;
}

/** Minimize the set of parents of every cluster transaction, without changing ancestry. */
template<typename S>
void WeedCluster(Cluster<S>& cluster, const AncestorSets<S>& ancs)
{
    std::vector<std::pair<unsigned, unsigned>> mapping(cluster.size());
    for (unsigned i = 0; i < cluster.size(); ++i) {
        mapping[i] = {ancs[i].Count(), i};
    }
    std::sort(mapping.begin(), mapping.end());
    for (unsigned i = 0; i < cluster.size(); ++i) {
        const auto& [_anc_count, idx] = mapping[i];
        S parents;
        S cover;
        cover.Add(idx);
        for (unsigned j = 0; j < i; ++j) {
            const auto& [_anc_count_j, idx_j] = mapping[i - 1 - j];
            if (ancs[idx][idx_j] && !cover[idx_j]) {
                parents.Add(idx_j);
                cover |= ancs[idx_j];
            }
        }
        assert(cover == ancs[idx]);
        cluster[idx].second = std::move(parents);
    }
}

/** Construct a new cluster with done removed (leaving the rest in order). */
template<typename S>
Cluster<S> TrimCluster(const Cluster<S>& cluster, const S& done)
{
    Cluster<S> ret;
    std::vector<unsigned> mapping;
    mapping.resize(cluster.size());
    ret.reserve(cluster.size() - done.Count());
    auto todo{(S::Full(cluster.size()) / done).Elements()};
    while (todo) {
        unsigned idx = todo.Next();
        mapping[idx] = ret.size();
        ret.push_back(cluster[idx]);
    }
    for (unsigned i = 0; i < ret.size(); ++i) {
        S parents;
        auto todo{ret[i].second.Elements()};
        while (todo) {
            unsigned idx = todo.Next();
            if (!done[idx]) {
                parents.Add(mapping[idx]);
            }
        }
        ret[i].second = std::move(parents);
    }
    return ret;
}

/** Minimize a cluster, and serialize to byte vector. */
template<typename S>
std::vector<unsigned char> DumpCluster(Cluster<S> cluster)
{
    AncestorSets<S> anc(cluster);
    WeedCluster(cluster, anc);
    std::vector<unsigned char> data;
    SerializeCluster(cluster, data);
    data.pop_back();
    return data;
}

/** Test whether an ancestor set was computed from an acyclic cluster. */
template<typename S>
bool IsAcyclic(const AncestorSets<S>& anc)
{
    for (unsigned i = 0; i < anc.Size(); ++i) {
        auto todo{anc[i].Elements()};
        // Determine if there is a j<i which i has as ancestor, and which has i as ancestor.
        while (todo) {
            unsigned j = todo.Next();
            if (j >= i) break;
            if (anc[j][i]) return false;
        }
    }
    return true;
}

} // namespace

} // namespace linearize_cluster

#endif // BITCOIN_CLUSTER_LINEARIZE_H
