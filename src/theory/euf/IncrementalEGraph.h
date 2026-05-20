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

namespace nlcolver {

struct PendingMerge {
    EufTermId a;
    EufTermId b;
    MergeReason reason;
};

struct ExplainContext;

class IncrementalEGraph {
public:
    explicit IncrementalEGraph(EufTermManager& tm);

    void clear();

    // Ensure term exists in UF and its canonical signature is registered.
    // Recursively registers signatures for all UF application subterms.
    // Enqueues any discovered congruence merges into outQueue.
    void ensureTermRegistered(EufTermId t, std::deque<PendingMerge>& outQueue);

    // UF unite + proof-forest + member-merge.
    // Registers new term signatures, refreshes affected parent signatures
    // (including congruence detection), all pushed to outQueue.
    MergeResult merge(EufTermId a, EufTermId b, const MergeReason& reason,
                      std::deque<PendingMerge>& outQueue);

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

    // Register signatures for all terms that have been interned but not yet
    // registered.  Discovered congruences are pushed into outQueue.
    void registerPendingSignatures(std::deque<PendingMerge>& outQueue);

    void setTrueTerm(EufTermId t) { trueTerm_ = t; }
    void setFalseTerm(EufTermId t) { falseTerm_ = t; }
    bool hasTrueFalseConflict() const;

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

    ExplainResult explainEquality(EufTermId a, EufTermId b, ExplainContext& ctx);
    ExplainResult explainEdge(size_t edgeId, ExplainContext& ctx);

    static uint64_t canonicalPairKey(EufTermId a, EufTermId b);

#ifndef NDEBUG
    void checkSignatureTableInvariant() const;
#endif
};

} // namespace nlcolver
