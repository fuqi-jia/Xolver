#include "theory/core/TheoryAtomRegistry.h"
#include <cassert>

namespace nlcolver {

void TheoryAtomRegistry::setContext(SatSolver* sat, DynamicAtomRegistrar* registrar) {
    sat_ = sat;
    registrar_ = registrar;
}

void TheoryAtomRegistry::observeIfNeeded(SatVar v) {
    if (observedVars_.insert(v).second) {
        sat_->addObservedVar(v);
    }
}

void TheoryAtomRegistry::registerParsedTheoryAtom(
    SatVar satVar,
    ExprId exprId,
    TheoryId theory,
    const TheoryAtomPayload& payload) {

    size_t idx = records_.size();
    records_.push_back({satVar, theory, false, exprId, payload});
    satVarToIdx_[satVar] = idx;
    observeIfNeeded(satVar);
}

SatLit TheoryAtomRegistry::getOrCreateLinearBoundAtom(
    const LinearFormKey& lhs,
    Relation rel,
    const mpq_class& rhs,
    TheoryId theory) {

    assert(sat_ != nullptr && registrar_ != nullptr &&
           "TheoryAtomRegistry::setContext must be called before getOrCreateLinearBoundAtom");

    LinearLookupKey key{lhs, rel, rhs};
    auto it = linearLookup_.find(key);
    if (it != linearLookup_.end()) {
        const auto& rec = records_[it->second];
        return SatLit::positive(rec.satVar);
    }

    ExprId expr = nextSyntheticExprId_++;
    SatLit lit = registrar_->registerDynamicAtom(expr, theory);

    size_t idx = records_.size();
    records_.push_back({lit.var, theory, true, expr, LinearAtomPayload{lhs, rel, rhs}});
    satVarToIdx_[lit.var] = idx;
    linearLookup_[key] = idx;
    observeIfNeeded(lit.var);

    return lit;
}

SatLit TheoryAtomRegistry::getOrCreatePolynomialAtom(
    PolyId poly,
    Relation rel,
    const mpq_class& rhs,
    TheoryId theory) {

    assert(sat_ != nullptr && registrar_ != nullptr &&
           "TheoryAtomRegistry::setContext must be called before getOrCreatePolynomialAtom");

    PolyLookupKey key{poly, rel, rhs};
    auto it = polyLookup_.find(key);
    if (it != polyLookup_.end()) {
        const auto& rec = records_[it->second];
        return SatLit::positive(rec.satVar);
    }

    ExprId expr = nextSyntheticExprId_++;
    SatLit lit = registrar_->registerDynamicAtom(expr, theory);

    size_t idx = records_.size();
    records_.push_back({lit.var, theory, true, expr,
                        PolynomialAtomPayload{poly, rel, RealValue::fromMpq(rhs)}});
    satVarToIdx_[lit.var] = idx;
    polyLookup_[key] = idx;
    observeIfNeeded(lit.var);

    return lit;
}

bool TheoryAtomRegistry::findByExprId(ExprId expr, LinearFormKey& outLhs,
                                       Relation& outRel, mpq_class& outRhs) const {
    for (const auto& rec : records_) {
        if (rec.exprId == expr) {
            if (std::holds_alternative<LinearAtomPayload>(rec.payload)) {
                const auto& p = std::get<LinearAtomPayload>(rec.payload);
                outLhs = p.lhs;
                outRel = p.rel;
                outRhs = p.rhs;
                return true;
            }
        }
    }
    return false;
}

const TheoryAtomRecord* TheoryAtomRegistry::findBySatVar(SatVar v) const {
    auto it = satVarToIdx_.find(v);
    if (it != satVarToIdx_.end()) {
        return &records_[it->second];
    }
    return nullptr;
}

SatLit TheoryAtomRegistry::getOrCreateSharedEqualityAtom(SharedTermId a, SharedTermId b) {
    assert(sat_ != nullptr && registrar_ != nullptr);

    // Canonical key: min(a,b), max(a,b)
    SharedTermId lo = a < b ? a : b;
    SharedTermId hi = a < b ? b : a;
    uint64_t key = (static_cast<uint64_t>(lo) << 32) | static_cast<uint64_t>(hi);

    auto it = sharedEqLookup_.find(key);
    if (it != sharedEqLookup_.end()) {
        const auto& rec = records_[it->second];
        return SatLit::positive(rec.satVar);
    }

    ExprId expr = nextSyntheticExprId_++;
    SatLit lit = registrar_->registerDynamicAtom(expr, TheoryId::Combination);

    size_t idx = records_.size();
    records_.push_back({lit.var, TheoryId::Combination, true, expr,
                        SharedEqualityPayload{a, b}});
    satVarToIdx_[lit.var] = idx;
    sharedEqLookup_[key] = idx;
    observeIfNeeded(lit.var);

    return lit;
}

} // namespace nlcolver
