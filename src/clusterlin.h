// Copyright (c) The Bitcoin Core developers
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
#include <tuple>
#include <deque>

#include <test/util/xoroshiro128plusplus.h>
#include <util/bitset.h>
#include <util/feefrac.h>
#include <util/ringbuffer.h>

#include <iostream>

namespace clusterlin {

/** Data type to represent cluster input.
 *
 * cluster[i].first is tx_i's fee and size.
 * cluster[i].second[j] is true iff tx_i spends one or more of tx_j's outputs.
 */
template<typename S>
using Cluster = std::vector<std::pair<FeeFrac, S>>;

/** Data structure that holds a transaction graph's preprocessed data (fee, size, ancestors,
 *  descendants). */
template<typename S>
struct DepGraph
{
    /** Information about a single transaction. */
    struct Entry
    {
        /** Fee and size of transaction itself. */
        FeeFrac feerate;
        /** All ancestors of the transaction (including itself). */
        S ancestors;
        /** All descendants of the transaction (including itself). */
        S descendants;

        friend bool operator==(const Entry&, const Entry&) noexcept = default;
        friend auto operator<=>(const Entry&, const Entry&) noexcept = default;

        Entry() noexcept = default;
        Entry(const FeeFrac& f, const S& a, const S& d) noexcept : feerate(f), ancestors(a), descendants(d) {}
    };

    /** Data for each transaction, in order. */
    std::vector<Entry> entries;

    // Comparison operators.
    friend bool operator==(const DepGraph&, const DepGraph&) noexcept = default;
    friend auto operator<=>(const DepGraph&, const DepGraph&) noexcept = default;

    /** Construct an empty DepGraph object. */
    DepGraph() noexcept = default;

    /** Construct a DepGraph objects for ntx transactions. */
    explicit DepGraph(unsigned ntx)
    {
        entries.resize(ntx);
        for (unsigned i = 0; i < ntx; ++i) {
            entries[i].ancestors = S::Singleton(i);
            entries[i].descendants = S::Singleton(i);
        }
    }

    /** Complete ancestors/descendant in this DepGraph.
     *
     * On input, entries[i].ancestors is expected to include at least i's direct parents, and
     * possibly other ancestors. entries[i].descendants can contain any of i's descendants,
     * including none.
     *
     * On output, entries[i].ancestors will be all of i's ancestors (including itself), and
     * entries[i].descendants will be all of i's descendants (including itself).
     */
    void PropagateAncestry() noexcept
    {
        // Propagate ancestor information.
        for (size_t i = 0; i < entries.size(); ++i) {
            // Make sure transactions are ancestors of themselves.
            entries[i].ancestors.Set(i);
            // At this point, entries[a].ancestors[b] is true iff:
            // - a != b, and b is an ancestor of a and there is a path from a to b through the
            //   subgraph consisting of {a, b} union {0, 1, ..., (i-1)}.
            // - a == b, and b<=i.
            S to_merge = entries[i].ancestors;
            for (size_t j = 0; j < entries.size(); ++j) {
                if (entries[j].ancestors[i]) {
                    entries[j].ancestors |= to_merge;
                }
            }
        }

        // Fill in descendant information.
        for (uint32_t i = 0; i < entries.size(); ++i) {
            for (auto j : entries[i].ancestors) {
                entries[j].descendants.Set(i);
            }
        }
    }

    /** Convert a cluster to a DepGraph (using the same order of transactions). */
    DepGraph(const Cluster<S>& cluster) noexcept : entries(cluster.size())
    {
        // Initialize feerate and ancestors (to direct parents + itself).
        for (size_t i = 0; i < cluster.size(); ++i) {
            entries[i].feerate = cluster[i].first;
            entries[i].ancestors = cluster[i].second;
        }
        // Compute full ancestor and descendant data.
        PropagateAncestry();
    }

    /** Get the number of transactions in the graph. */
    auto TxCount() const noexcept { return entries.size(); }
    /** Get the feerate of a given transaction i. */
    const FeeFrac& FeeRate(unsigned i) const noexcept { return entries[i].feerate; }
    /** Get the ancestors of a given transaction i. */
    const S& Ancestors(unsigned i) const noexcept { return entries[i].ancestors; }
    /** Get the descendants of a given transaction i. */
    const S& Descendants(unsigned i) const noexcept { return entries[i].descendants; }

    /** Modify this transaction graph, adding a dependency between a specified parent and child. */
    void AddDependency(unsigned parent, unsigned child) noexcept
    {
        // To each ancestor of the parent, add as descendants the descendants of the child.
        const auto& chl_des = entries[child].descendants;
        for (auto anc_of_par : Ancestors(parent)) {
            entries[anc_of_par].descendants |= chl_des;
        }
        // To each descendant of the child, add as ancestors the ancestors of the parent.
        const auto& par_anc = entries[parent].ancestors;
        for (auto dec_of_chl : Descendants(child)) {
            entries[dec_of_chl].ancestors |= par_anc;
        }
    }

    /** Get the minimal set of parents a transaction has (parents which are not parents
     *  of ancestors). */
    S GetReducedParents(unsigned i) const noexcept
    {
        S ret = Ancestors(i);
        ret.Reset(i);
        for (auto a : ret) {
            if (ret[a]) {
                ret /= Ancestors(a);
                ret.Set(a);
            }
        }
        return ret;
    }

    /** Get the minimal set of children a transaction has (children which are not children
     *  of descendants). */
    S GetReducedChildren(unsigned i) const noexcept
    {
        S ret = Descendants(i);
        ret.Reset(i);
        for (auto a : ret) {
            if (ret[a]) {
                ret /= Descendants(a);
                ret.Set(a);
            }
        }
        return ret;
    }

    /** Compute the aggregate feerate of a set of nodes in this graph. */
    FeeFrac FeeRate(const S& elems) const noexcept
    {
        FeeFrac ret;
        for (auto pos : elems) ret += entries[pos].feerate;
        return ret;
    }

    /** Check if this graph is acyclic. */
    bool IsAcyclic() const noexcept
    {
        for (size_t i = 0; i < TxCount(); ++i) {
            if ((Ancestors(i) & Descendants(i)) != S::Singleton(i)) {
                return false;
            }
        }
        return true;
    }

    /** Find some connected component within the subset "left" of this graph. */
    S FindConnectedComponent(const S& left) const noexcept
    {
        if (left.None()) return left;
        auto first = left.First();
        S ret = Descendants(first) | Ancestors(first);
        ret &= left;
        S to_add = ret;
        to_add.Reset(first);
        do {
            S old = ret;
            for (auto add : to_add) {
                ret |= Descendants(add);
                ret |= Ancestors(add);
            }
            ret &= left;
            to_add = ret / old;
        } while (to_add.Any());
        return ret;
    }

    /** Determine if this entire graph is connected. */
    bool IsConnected() const noexcept
    {
        return FindConnectedComponent(S::Fill(TxCount())) == S::Fill(TxCount());
    }

};

template<typename S>
std::vector<S> FindKernels(const DepGraph<S>& depgraph)
{
    std::vector<S> ret;

    struct WorkItem
    {
        S inc, exc;

        WorkItem(const S& i, const S& e) noexcept : inc(i), exc(e) {}
    };

    std::vector<WorkItem> queue;
    queue.emplace_back(S{}, S{});
    const S todo = S::Fill(depgraph.TxCount());

    // Create a new WorkItem, starting from given inc/exc, and adding/removing to_add/to_del.
    auto add_fn = [&](S inc, S exc, S to_add, S to_del) noexcept {
        // The out-of-kernel ancestors and descendants.
        S anc, des;
        if (inc.Any()) {
            anc = depgraph.Ancestors(inc.First()) / inc;
            des = depgraph.Descendants(inc.First()) / inc;
        }
        // Add entries to the kernel while there are any.
        while (to_add.Any()) {
            auto add = to_add.First();
            to_add.Reset(add);
            const auto& add_anc = depgraph.Ancestors(add);
            const auto& add_des = depgraph.Descendants(add);
            if (inc.Any()) {
                // For any two transactions in the kernel (one in inc, and add), any ancestor of
                // one that is not an ancestor of both must be part of the kernel (as these two
                // would have distinct out-of-kernel ancestors otherwise).
                to_add |= anc ^ add_anc;
                // Likewise, with descendants.
                to_add |= des ^ add_des;
                to_add /= inc;
                to_add.Reset(add);
            } else {
                // When the first transaction is added to the kernel, reprocess all the previously
                // excluded ones (as these may trigger many more exclusions).
                to_del |= exc;
            }
            inc.Set(add);
            anc = (anc | add_anc) / inc;
            des = (des | add_des) / inc;
            // Abort when inconsistent.
            if ((inc | to_add) && (exc | to_del)) return;
        }
        while (to_del.Any()) {
            auto del = to_del.First();
            to_del.Reset(del);
            exc.Set(del);
            const auto& del_anc = depgraph.Ancestors(del);
            const auto& del_des = depgraph.Descendants(del);
            if (del_des && inc) {
                to_del |= todo / del_des;
            } else if (del_anc && inc) {
                to_del |= todo / del_anc;
            } else {
                to_del |= del_anc & anc;
                to_del |= del_des & des;
            }
            to_del /= exc;
            if (inc && (exc | to_del)) return;
        }
        queue.emplace_back(inc, exc);
    };

    while (!queue.empty()) {
        S inc = std::move(queue.back().inc);
        S exc = std::move(queue.back().exc);
        queue.pop_back();

        auto left = (todo / (inc | exc));

        std::optional<unsigned> split;
        if (left.Any()) {
            if (inc.Any()) {
                unsigned first = inc.First();
                S cand = (depgraph.Descendants(first) | depgraph.Ancestors(first)) & left;
                if (cand.Any()) {
                    split = cand.First();
                }
            } else {
                split = left.First();
            }
        }

        if (!split.has_value()) {
            if (inc != todo && inc.Count() > 1) {
                ret.push_back(inc);
            }
            continue;
        }

        // Construct work item with split included.
        add_fn(inc, exc, S::Singleton(*split), {});

        // Construct work item with split excluded.
        add_fn(inc, exc, {}, S::Singleton(*split));
    }

    std::sort(ret.begin(), ret.end());
    return ret;
}

template<typename S>
class Linearizer
{
    DepGraph<S> m_depgraph;
    std::vector<uint32_t> m_new_to_old;

public:
    Linearizer(const Cluster<S>& cluster) : m_new_to_old(cluster.size())
    {
        m_depgraph.entries.resize(cluster.size());
        // Determine reordering mapping, by sorting by decreasing feerate.
        std::iota(m_new_to_old.begin(), m_new_to_old.end(), uint32_t{0});
        std::sort(m_new_to_old.begin(), m_new_to_old.end(), [&](uint32_t a, uint32_t b) {
            auto feerate_cmp = cluster[a].first <=> cluster[b].first;
            if (feerate_cmp == 0) return a < b;
            return feerate_cmp > 0;
        });
        // Compute reverse mapping.
        std::vector<uint32_t> old_to_new(cluster.size());
        for (size_t i = 0; i < cluster.size(); ++i) {
            old_to_new[m_new_to_old[i]] = i;
        }
        // Construct initial txdata.
        for (size_t i = 0; i < cluster.size(); ++i) {
            m_depgraph.entries[i].feerate = cluster[m_new_to_old[i]].first;
            for (auto par : cluster[m_new_to_old[i]].second) {
                m_depgraph.entries[i].ancestors.Set(old_to_new[par]);
            }
        }
        // Compute ancestors/descendants.
        m_depgraph.PropagateAncestry();
    }

    S MapBack(const S& arg) noexcept
    {
        S ret;
        for (auto pos : arg) ret.Set(m_new_to_old[pos]);
        return ret;
    }

    /** Find the highest-feerate topologically-valid subset of todo.
     *
     * Note that todo and the return value both correspond to the reordered transaction list.
     */
    S FindBestCandidate(const S todo, uint64_t rng_seed) noexcept
    {
        // Bail out quickly if we're given a (remaining) cluster that is empty.
        if (todo.None()) return todo;

        /** Type for work queue items. */
        struct WorkItem
        {
            /** Set of transactions definitely included. This must be a subset of todo, and be
             *  topologically valid (includes all in-todo ancestors of itself). */
            S inc;
            /** Set of undecided transactions. This must be a subset of todo, and have no overlap
             *  with inc. The set (inc | und) must be topologically valid. */
            S und;
            /** The best (=highest feerate, and smallest as tiebreaker) superset of inc and subset
             *  of (inc | und). It does not need to be topologically valid. If inc is empty then
             *  pot must be empty too (to guarantee the property that every element of (pot / inc)
             *  has higher feerate than pot itself, see further). */
            S pot;
            /** Equal to m_depgraph.FeeRate(inc). */
            FeeFrac inc_feerate;
            /** Equal to m_depgraph.FeeRate(pot). */
            FeeFrac pot_feerate;
            /** Construct a new work item. */
            WorkItem(S&& i, S&& u, S&& p, FeeFrac&& i_f, FeeFrac&& p_f) noexcept :
                inc(std::move(i)), und(std::move(u)), pot(std::move(p)),
                inc_feerate(std::move(i_f)), pot_feerate(std::move(p_f)) {}
            /** Swap two WorkItems. */
            void swap(WorkItem& other) noexcept
            {
                std::swap(inc, other.inc);
                std::swap(und, other.und);
                std::swap(pot, other.pot);
                std::swap(inc_feerate, other.inc_feerate);
                std::swap(pot_feerate, other.pot_feerate);
            }
        };

        /** The queue of work items. */
        XoRoShiRo128PlusPlus rng(rng_seed);
        RingBuffer<WorkItem> queue;
        queue.reserve(std::max<size_t>(256, 2 * todo.Count()));

        /** The best candidate set found so far (initialized in component-finding below). */
        S best;
        /** The feerate of best_candidate. */
        FeeFrac best_feerate;

        /** The set of transactions in todo which have feerate > best_feerate. */
        S imp;

        /** Internal function to add a work item.
         *
         * - inc: the "inc" value for the new work item
         * - und: the "und" value for the new work item
         * - pot: a subset of the "pot" value for the new work item (but a superset of inc).
         *        Missing transactions will be added automatically by add_fn.
         * - inc_feerate: equal to m_depgraph.FeeRate(inc)
         * - pot_feerate: equal to m_depgraph.FeeRate(pot)
         * - consider_inc: a subset of (pot / inc) of transactions to consider adding to inc, if it
         *                 can be proven they must be part of the best topologically valid superset
         *                 of inc and subset of (inc | und). Transactions that are missing from
         *                 pot are automatically considered for addition to inc.
         */
        auto add_fn = [&](S inc, S und, S pot, FeeFrac inc_feerate, FeeFrac pot_feerate, S consider_inc) noexcept {
            Assume(inc << todo);
            Assume(und << todo);
            Assume(!(inc && und));
            Assume(pot >> inc);
            Assume(pot << (inc | und));
            Assume(pot.None() == inc.None());
            Assume(consider_inc << (pot / inc));

            if (inc_feerate.IsEmpty()) {
                // If inc is empty, we leave pot/pot_feerate empty too, and don't compare it with
                // best_feerate (see split_fn); instead, just make sure there are undecided
                // transactions left to split on.
                if (und.None()) return;
            } else {
                // Add missing entries to pot (and pot_feerate). We iterate over all undecided transactions
                // excluding pot whose feerate is higher than best_feerate.
                for (auto pos : (imp & und) / pot) {
                    // Determine if adding transaction pos to pot (ignoring topology) would improve it. If
                    // not, we're done updating pot.
                    if (!(m_depgraph.FeeRate(pos) >> pot_feerate)) break;
                    pot_feerate += m_depgraph.FeeRate(pos);
                    pot.Set(pos);
                    consider_inc.Set(pos);
                }

                // The "jump ahead" optimization:
                //
                // Let S be the set of sets T of transactions for which T is topologically valid, T
                // is a superset of inc and T is a subset of (inc | und). In other words, S
                // contains all possible "inc"s compatible with the work item currently being added.
                //
                // Let B be the best element of S, so B is the highest-feerate (tie-breaking using
                // smallest size) inc compatible with the work item being added.
                //
                // It now holds that any topologically-valid subset of pot must be a subset of B.
                // To see why:
                // - Every element of (pot / inc) has a feerate higher than any element of S:
                //   - The feerate of every element of (pot / inc) is strictly higher than that of
                //     pot in its entirety. This clearly holds for the last item added to it (or it
                //     would not have been added), and all earlier items have a feerate at least as
                //     high as the last-added one.
                //   - Every element of (pot / inc) has a feerate strictly higher than inc in its
                //     entirety. This follows from the previous point and the fact that inc is not
                //     empty.
                //   - The feerate of every element of (und / pot) is less or equal to that of pot.
                //     Otherwise the first one of them would have been added to pot.
                //   - All together, elements of (pot / inc) have higher feerate than inc, and thus
                //     also higher feerate than inc completement with any subset of (und / inc).
                // - Thus, for any element T of S, adding any non-empty subset of (pot / T) to it
                //   strictly increases its feerate.
                // - No set C which is a topologically valid subset of pot can exist which is not
                //   also a subset of B.
                //   - B and C are both topologically valid, thus (B | C) is also topologically
                //     valid.
                //   - (C / B) is non-empty (because C is not a subset of B), and a subset of
                //     (pot / B), thus from the previous point it follows that (C / B) has higher
                //     feerate than B.
                //   - Thus, (B | C) is topologically valid and has a higher feerate than B. This
                //     is in contradiction with the fact that B is the highest-feerate element of
                //     S.
                //
                // As a result we can look for topologically valid subsets of pot that are not
                // subsets of inc, and union them into inc. We do so by checking the ancestry of
                // any element of consider_inc.
                const S init_inc = inc;
                for (auto pos : consider_inc) {
                    // If the transaction's ancestors are a subset of pot, we can merge it
                    // together with its ancestors to inc.
                    auto anc_todo = m_depgraph.Ancestors(pos) & todo;
                    if (pot >> anc_todo) inc |= anc_todo;
                }
                // Finally update und and inc_feerate to account for the added transactions.
                und /= inc;
                inc_feerate += m_depgraph.FeeRate(inc / init_inc);

                // If inc_feerate is better than best_feerate, remember inc as our new best.
                if (inc_feerate > best_feerate) {
                    best_feerate = inc_feerate;
                    best = inc;
                    // See if we can remove any entries from imp now.
                    while (imp.Any()) {
                        unsigned check = imp.Last();
                        if (m_depgraph.FeeRate(check) >> best_feerate) break;
                        imp.Reset(check);
                    }
                }

                // If no potential transactions exist beyond the already included ones, no improvement
                // is possible anymore.
                if (pot == inc) return;
                // At this point und must be non-empty. If it were empty then pot would equal inc.
                Assume(und.Any());
            }

            // Actually construct new work item on the queue.
            queue.emplace_back(std::move(inc), std::move(und), std::move(pot), std::move(inc_feerate), std::move(pot_feerate));
        };

        /** Internal process function. It takes an existing work item, and splits it in two: one
         *  with a particular transaction (and its ancestors) included, and one with that
         *  transaction (and its descendants) excluded. */
        auto split_fn = [&](WorkItem&& elem) noexcept {
            // Any queue element must have undecided transactions left, otherwise there is nothing
            // to explore anymore.
            Assume(elem.und.Any());
            // The potential set must include the included set, and be a subset of (und | inc).
            Assume((elem.pot >> elem.inc) && (elem.pot << (elem.und | elem.inc)));
            // The potential, undecided, and (implicitly) included set are all subsets of todo.
            Assume((todo >> elem.pot) && (todo >> elem.und));
            // Included transactions cannot be undecided.
            Assume(!(elem.inc && elem.und));
            // If pot is empty, then so is inc.
            Assume(elem.inc_feerate.IsEmpty() == elem.pot_feerate.IsEmpty());

            // We can ignore any queue item whose potential feerate isn't better than the best seen
            // so far.
            const unsigned first = elem.und.First();
            if (!elem.pot_feerate.IsEmpty()) {
                if (elem.pot_feerate <= best_feerate) return;
            } else {
                // In case inc/pot are empty, use a simpler alternative check.
                if (m_depgraph.FeeRate(first) <= best_feerate) return;
            }

            // Decide which transaction to split on (create new work items; one with it included, one
            // with it excluded).
            //
            // Among the (undecided) ancestors of the highest individual feerate transaction, pick the
            // one which reduces the search space most:
            // - Minimizes the size of the largest of the undecided sets after including or excluding.
            // - If the above is equal, the one that minimizes the other branch's undecided set size.
            // - If the above are equal, the one with the best individual feerate.
            unsigned pos = 0;
            const auto select = elem.und & m_depgraph.Ancestors(first);
            Assume(select.Any());
            std::optional<std::pair<unsigned, unsigned>> pos_counts;
            for (auto i : select) {
                std::pair<unsigned, unsigned> counts{
                    (elem.und / m_depgraph.Ancestors(i)).Count(),
                    (elem.und / m_depgraph.Descendants(i)).Count()};
                if (counts.first < counts.second) std::swap(counts.first, counts.second);
                if (!pos_counts.has_value() || counts < *pos_counts) {
                    pos = i;
                    pos_counts = counts;
                }
            }
            // Since there was at least one transaction in select, we must always find one.
            Assume(pos_counts.has_value());

            // Consider adding a work item corresponding to that transaction included.
            const auto anc = m_depgraph.Ancestors(pos) & todo;
            const auto new_inc = elem.inc | anc;
            add_fn(/*inc=*/new_inc,
                   /*und=*/elem.und / anc,
                   /*pot=*/elem.pot | anc,
                   /*inc_feefrac=*/elem.inc_feerate + m_depgraph.FeeRate(anc / elem.inc),
                   /*pot_feefrac=*/elem.pot_feerate + m_depgraph.FeeRate(anc / elem.pot),
                   /*consider_inc=*/elem.pot / new_inc);

            // Consider adding a work item corresponding to that transaction excluded.
            const auto& desc = m_depgraph.Descendants(pos);
            add_fn(/*inc=*/elem.inc,
                   /*und=*/elem.und / desc,
                   /*pot=*/elem.pot / desc,
                   /*inc_feefrac=*/elem.inc_feerate,
                   /*pot_feefrac=*/elem.pot_feerate - m_depgraph.FeeRate(elem.pot & desc),
                   /*consider_inc=*/{});
        };

        // Create an initial entry per connected component of todo.
        auto to_cover = todo;
        do {
            auto component = m_depgraph.FindConnectedComponent(to_cover);
            auto component_feerate = m_depgraph.FeeRate(component);
            // Start with best_feerate equal to the highest component's feerate. This avoids the
            // need to deal with the special case of best_feerate being empty inside add_fn.
            if (best_feerate.IsEmpty() || component_feerate > best_feerate) {
                best = component;
                best_feerate = component_feerate;
            }
            to_cover /= component;
            queue.emplace_back(/*i=*/S{}, /*u=*/std::move(component), /*p=*/S{}, /*i_f=*/FeeFrac{}, /*p_f=*/FeeFrac{});
        } while (to_cover.Any());

        // Initialize imp.
        imp = todo;
        do {
            auto check = imp.Last();
            if (m_depgraph.FeeRate(check) >> best_feerate) break;
            imp.Reset(check);
        } while(imp.Any());

        // Work processing loop.
        while (!queue.empty()) {
            // Randomly swap the first two items to provide unpredictability.
            if (queue.size() > 1 && rng() & 1) queue[0].swap(queue[1]);

            // Determine how small queue.size() has to get before we can process the first entry.
            size_t queuesize_for_front = queue.capacity() - queue.front().und.Count() - 1;

            // Process entries from the end of the queue (DFS exploration) until it shrinks below.
            while (queue.size() > queuesize_for_front) {
                auto elem = queue.back();
                queue.pop_back();
                split_fn(std::move(elem));
            }

            // Process one entry from the front of the queue (BFS exploration)
            auto elem = queue.front();
            queue.pop_front();
            split_fn(std::move(elem));
        }

        return best;
    }

    const DepGraph<S>& GetDepGraph() const noexcept { return m_depgraph; }
};

} // namespace clusterlin

#endif
