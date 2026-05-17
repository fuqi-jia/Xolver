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
    void ensureTerm(EufTermId t);

    // 执行一次 UF unite + proof-forest + member-merge。
    // 不 refresh congruence，不 drain queue。
    MergeResult merge(EufTermId a, EufTermId b, const MergeReason& reason);

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

    void setTrueTerm(EufTermId t) { trueTerm_ = t; }
    void setFalseTerm(EufTermId t) { falseTerm_ = t; }
    bool hasTrueFalseConflict() const;

private:
    EufTermManager& tm_;
    RollbackUnionFind uf_;

    std::vector<std::vector<EufTermId>> members_;
    std::vector<MemberChange> memberTrail_;
    std::vector<MergeRecord> mergeRecords_;

    // 内部保留的 queue，仅用于兼容旧路径（如有），EufSolver 不再调用 processMergeQueue。
    std::deque<PendingMerge> mergeQueue_;

    RollbackSignatureTable sigTable_;
    std::vector<std::optional<AppSignature>> currentSig_;
    std::vector<std::pair<EufTermId, std::optional<AppSignature>>> currentSigTrail_;

    ProofForest proofForest_;

    EufTermId trueTerm_ = NullEufTerm;
    EufTermId falseTerm_ = NullEufTerm;
    EufTermId nextTermToRegister_ = 0;

    AppSignature computeSignature(EufTermId t) const;
    void refreshSignature(EufTermId app, std::deque<PendingMerge>* outQueue);
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
