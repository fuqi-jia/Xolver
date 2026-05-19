#include "frontend/atomization/EufAtomExtractor.h"
#include "theory/TheoryAtomRegistry.h"
#include "expr/ir.h"

namespace nlcolver {

SatLit EufAtomExtractor::getOrCreateAtom(
    const EufAtomPayload& payload,
    ExprId originExpr,
    std::unordered_map<ExprId, SatLit>& memo,
    const std::function<SatVar()>& freshVar,
    const std::function<void(SatVar, ExprId, bool, TheoryId)>& recordAtom)
{
    EufAtomPayload canon = payload;
    if (canon.lhs > canon.rhs) {
        std::swap(canon.lhs, canon.rhs);
    }

    EufAtomKey key{canon.lhs, canon.rhs, canon.rel, canon.kind};
    auto it = dedup_.find(key);
    if (it != dedup_.end()) {
        memo[originExpr] = it->second;
        return it->second;
    }

    SatVar v = freshVar();
    SatLit lit = SatLit::positive(v);
    recordAtom(v, originExpr, true, TheoryId::EUF);
    dedup_[key] = lit;
    memo[originExpr] = lit;

    if (registry_) {
        registry_->registerParsedTheoryAtom(v, originExpr, TheoryId::EUF, canon);
    }

    return lit;
}

SatLit EufAtomExtractor::atomizeNaryEq(
    ExprId eid, const CoreIr& ir,
    std::unordered_map<ExprId, SatLit>& memo,
    const std::function<SatVar()>& freshVar,
    const std::function<void(const std::vector<SatLit>&)>& addClause,
    const std::function<SatLit(ExprId)>& atomizeRec)
{
    const auto& e = ir.get(eid);

    SatVar andVar = freshVar();
    std::vector<SatLit> pairwiseLits;

    for (size_t i = 0; i + 1 < e.children.size(); ++i) {
        ExprId lhs = e.children[i];
        ExprId rhs = e.children[i + 1];
        SatLit plit = getOrCreateAtom(
            EufAtomPayload{lhs, rhs, Relation::Eq}, eid,
            memo, freshVar,
            [](SatVar, ExprId, bool, TheoryId) { /* n-ary pairwise already recorded by getOrCreateAtom */ });
        pairwiseLits.push_back(plit);
    }

    // Tseitin: andVar → each pairwise
    for (SatLit pl : pairwiseLits) {
        addClause({SatLit::negative(andVar), pl});
    }
    // Tseitin: any pairwise → andVar
    std::vector<SatLit> clause;
    clause.push_back(SatLit::positive(andVar));
    for (SatLit pl : pairwiseLits) {
        clause.push_back(pl.negated());
    }
    addClause(clause);

    return SatLit::positive(andVar);
}

SatLit EufAtomExtractor::atomizeNaryDistinct(
    ExprId eid, const CoreIr& ir,
    std::unordered_map<ExprId, SatLit>& memo,
    const std::function<SatVar()>& freshVar,
    const std::function<void(const std::vector<SatLit>&)>& addClause,
    const std::function<SatLit(ExprId)>& atomizeRec)
{
    const auto& e = ir.get(eid);

    if (e.children.size() <= 1) {
        SatVar tv = freshVar();
        addClause({SatLit::positive(tv)});
        return SatLit::positive(tv);
    }

    SatVar andVar = freshVar();
    std::vector<SatLit> pairwiseLits;

    for (size_t i = 0; i < e.children.size(); ++i) {
        for (size_t j = i + 1; j < e.children.size(); ++j) {
            ExprId lhs = e.children[i];
            ExprId rhs = e.children[j];
            SatLit plit = getOrCreateAtom(
                EufAtomPayload{lhs, rhs, Relation::Neq}, eid,
                memo, freshVar,
                [](SatVar, ExprId, bool, TheoryId) { /* n-ary pairwise already recorded */ });
            pairwiseLits.push_back(plit);
        }
    }

    // Tseitin AND encoding
    for (SatLit pl : pairwiseLits) {
        addClause({SatLit::negative(andVar), pl});
    }
    std::vector<SatLit> clause;
    clause.push_back(SatLit::positive(andVar));
    for (SatLit pl : pairwiseLits) {
        clause.push_back(pl.negated());
    }
    addClause(clause);

    return SatLit::positive(andVar);
}

} // namespace nlcolver
