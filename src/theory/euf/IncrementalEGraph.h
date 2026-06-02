#pragma once
#include "theory/euf/EufTypes.h"
#include "theory/euf/EufTermManager.h"
#include "theory/euf/RollbackUnionFind.h"
#include "theory/euf/RollbackSignatureTable.h"
#include "theory/euf/ProofForest.h"
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <deque>
#include <optional>
#include <cstdint>

namespace xolver {

struct PendingMerge {
    EufTermId a;
    EufTermId b;
    MergeReason reason;
    // Decision level this merge belongs to. Asserted/interface merges carry
    // their literal's level; congruence/array merges generated during saturation
    // inherit the level of the merge that triggered them. The EUF saturation
    // processes merges in ascending level order, so the egraph's size-based undo
    // trail stays aligned with decision-level backtrack boundaries. (Interface
    // equalities can be injected out of record order, so record order alone is
    // not a reliable proxy for level — A4's combination note.)
    int level = 0;
};

class IncrementalEGraph {
public:
    explicit IncrementalEGraph(EufTermManager& tm);

    void clear();

    // Ensure term exists in UF and its canonical signature is registered.
    // Registers signatures for all UF application subterms (iterative post-order
    // over the arg DAG — must not recurse; deep UF nesting overflows the stack).
    // Enqueues any discovered congruence merges into outQueue.
    void ensureTermRegistered(EufTermId t, std::deque<PendingMerge>& outQueue);

    // UF unite + proof-forest + member-merge.
    // Registers new term signatures, refreshes affected parent signatures
    // (including congruence detection), all pushed to outQueue.
    // `level` is the SAT decision level at which the merge is caused — stored
    // on the resulting MergeRecord (and propagated to the proof-forest trail)
    // so EufSolver::backtrackToLevel can run a level-FILTER cleanup pass to
    // catch records and edges whose level > target but were inserted out of
    // monotonic order (combination interface eq breaks the monotonic
    // assumption that count-based snapshot rollback alone relies on).
    MergeResult merge(EufTermId a, EufTermId b, const MergeReason& reason,
                      int level,
                      std::deque<PendingMerge>& outQueue);
    // 3-arg overload (level defaulted to 0): preserves legacy unit-test call
    // sites that don't exercise multi-level backtrack. Production callers in
    // EufSolver::applyMerge always pass the explicit level via the 4-arg form.
    MergeResult merge(EufTermId a, EufTermId b, const MergeReason& reason,
                      std::deque<PendingMerge>& outQueue) {
        return merge(a, b, reason, 0, outQueue);
    }

    // 扫描 kept/killed 的 parents，refresh signature，
    // 把发现的 congruence merges 推到 outQueue。
    void refreshCongruence(EClassId kept, EClassId killed,
                           std::deque<PendingMerge>& outQueue);

    bool same(EufTermId a, EufTermId b) const;
    EClassId rep(EufTermId t) const;

    EGraphSnapshot snapshot() const;
    void rollback(EGraphSnapshot snap);

    ExplainResult explainEquality(EufTermId a, EufTermId b);

    size_t mergeRecordCount() const { return mergeRecords_.size(); }
    const MergeRecord& mergeRecord(size_t i) const { return mergeRecords_[i]; }

    // Read-only access to the proof forest for invariant audit (UFE soundness
    // gate). Used by EufSolver::checkProofForestInvariants to walk every
    // reachable edge and verify its reason is consistent with the current trail.
    const ProofForest& proofForest() const { return proofForest_; }

    // Mutable access used by EufSolver::backtrackToLevel for the level-filter
    // cleanup pass (rollbackByLevel). Keep narrow — do NOT use elsewhere; the
    // proof forest is otherwise modified only through merge() / rollback().
    ProofForest& proofForestMutable() { return proofForest_; }

    // Drop trailing mergeRecords_ whose level > targetLevel. Used in tandem
    // with proofForestMutable().rollbackByLevel(target) to clean up entries
    // that survived the count-based snapshot rollback because they were
    // inserted out of monotonic level order (combination interface eq class).
    // Only drops from the END — an entry with level > target before a kept
    // entry would be a different bug class (the level-tagging discipline
    // breaks). Sound by construction: dropped records were already disabled
    // in the union-find by the snapshot rollback.
    void dropMergeRecordsAboveLevel(int targetLevel) {
        while (!mergeRecords_.empty() && mergeRecords_.back().level > targetLevel) {
            mergeRecords_.pop_back();
        }
    }

    // Register signatures for all terms that have been interned but not yet
    // registered.  Discovered congruences are pushed into outQueue.
    void registerPendingSignatures(std::deque<PendingMerge>& outQueue);

    void setTrueTerm(EufTermId t) { trueTerm_ = t; }
    void setFalseTerm(EufTermId t) { falseTerm_ = t; }
    bool hasTrueFalseConflict() const;

    // Access members of an equivalence class (for constant evaluation)
    const std::vector<EufTermId>& classMembers(EClassId c) const {
        static const std::vector<EufTermId> empty;
        return c < members_.size() ? members_[c] : empty;
    }

#ifndef NDEBUG
    // Verify that every app term has a registered signature matching its
    // canonical signature, and all terms with the same canonical signature
    // are in the same equivalence class.  Does NOT skip terms with missing
    // currentSig_ — a missing signature is a bug.
    bool congruenceClosed() const;
#endif

private:
    EufTermManager& tm_;
    RollbackUnionFind uf_;

    // After a merge, refresh signatures for parents of the LOSER class only —
    // their members' representative just changed. The winner class's parents
    // keep the same representative, so their canonical signatures are
    // unchanged; re-scanning them is duplicate work that re-discovers already-
    // known congruences and pushes redundant merge requests to the queue.
    //
    // Default-ON (agent/eqna-2 E2/E3 profile task, 2026-06-01): QG7 profile
    // showed saturation = 94% of EUF check() time. Loser-only walk gives ~4×
    // throughput on QG7 (1577us → 352us per check), +1/30 QG paired recovery,
    // 0 lost on QG/eq_diamond/full reg/units. The XOLVER_UF_FAST_CC envvar
    // remains as an A/B escape (=0 disables); the mathematical correctness
    // is the proof of soundness — see comment block in
    // IncrementalEGraph::merge.
    bool fastMerge_ = true;

    std::vector<std::vector<EufTermId>> members_;
    std::vector<MemberChange> memberTrail_;
    std::vector<MergeRecord> mergeRecords_;

    RollbackSignatureTable sigTable_;
    std::vector<std::optional<AppSignature>> currentSig_;
    std::vector<std::pair<EufTermId, std::optional<AppSignature>>> currentSigTrail_;

    ProofForest proofForest_;

    EufTermId trueTerm_ = NullEufTerm;
    EufTermId falseTerm_ = NullEufTerm;
    EufTermId nextTermToRegister_ = 0;

    // Allocate UF node and resize aux vectors.  Does NOT register signature.
    void ensureNodeAllocated(EufTermId t);

    AppSignature computeSignature(EufTermId t) const;

    // Refresh canonical signature for app term.  Always pushes discovered
    // congruences to outQueue.  Never uses an internal queue.
    //
    // CRITICAL invariants:
    //   1. If a valid owner with the same canonical signature already exists,
    //      enqueue a congruence merge but do NOT replace the owner.
    //   2. If no valid owner exists, app becomes the owner.
    //   3. currentSig_ and sigTable_ are always kept consistent.
    void refreshSignature(EufTermId app, std::deque<PendingMerge>& outQueue);

    void setCurrentSig(EufTermId app, std::optional<AppSignature> sig);
    void rollbackCurrentSig(size_t snap);
    std::vector<EufTermId> collectParents(EClassId root) const;

    static uint64_t canonicalPairKey(EufTermId a, EufTermId b);

#ifndef NDEBUG
    void checkSignatureTableInvariant() const;
#endif
};

} // namespace xolver
