#include "theory/core/TheoryAtomRegistry.h"
#include <cassert>

namespace xolver {

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
    if (exprId != NullExpr) exprIdToIdxs_[exprId].push_back(idx);  // iter-101 perf
    observeIfNeeded(satVar);

    // Populate the (poly,rel,rhs) / (linear,rel,rhs) lookup maps so a
    // later getOrCreate* call for the SAME canonical atom REUSES this
    // SatVar instead of allocating a fresh one. Without this:
    //   • Two syntactically-different but semantically-equivalent atoms
    //     (e.g. `(= 0 (+ a b))` parsed AND `(= (+ a b) 0)` synthesized
    //     by a linearization cut) get DIFFERENT SatVars.
    //   • SAT enumerates assignments where one is true and the other
    //     false; conflict clauses learned for one don't transfer to
    //     the other.
    //   • UNSAT proofs that hinge on recognizing two SAT vars as the
    //     same atom never close.
    // This is the "same value used different ids" pathology.
    //
    // If a canonical key already exists for a DIFFERENT SatVar (rare
    // for parsed atoms but possible when parser-side preprocessing
    // collapses different parser nodes to the same canonical poly),
    // wire `S_new <-> S_existing` so SAT keeps them in lockstep.
    auto wireEquivalence = [&](SatVar a, SatVar b) {
        if (!sat_ || a == b) return;
        sat_->addClause({SatLit::negative(a), SatLit::positive(b)});
        sat_->addClause({SatLit::positive(a), SatLit::negative(b)});
    };

    if (std::holds_alternative<PolynomialAtomPayload>(payload)) {
        const auto& p = std::get<PolynomialAtomPayload>(payload);
        auto rhsQ = p.rhs.tryAsRational();
        if (rhsQ) {
            PolyLookupKey key{p.poly, p.rel, *rhsQ};
            auto it = polyLookup_.find(key);
            if (it == polyLookup_.end()) {
                polyLookup_[key] = idx;
            } else {
                const auto& existing = records_[it->second];
                wireEquivalence(satVar, existing.satVar);
            }
        }
    } else if (std::holds_alternative<LinearAtomPayload>(payload)) {
        const auto& p = std::get<LinearAtomPayload>(payload);
        auto rhsQ = p.rhs.tryAsRational();
        if (rhsQ) {
            LinearLookupKey key{p.lhs, p.rel, *rhsQ};
            auto it = linearLookup_.find(key);
            if (it == linearLookup_.end()) {
                linearLookup_[key] = idx;
            } else {
                const auto& existing = records_[it->second];
                wireEquivalence(satVar, existing.satVar);
            }
        }
    }
}

void TheoryAtomRegistry::pinLiteral(SatVar satVar, bool value) {
    if (!sat_) return;
    sat_->addClause({value ? SatLit::positive(satVar) : SatLit::negative(satVar)});
}

void TheoryAtomRegistry::registerBoolVariable(const std::string& name, SatVar satVar) {
    boolVarSatVars_[name] = satVar;
}

std::optional<SatVar>
TheoryAtomRegistry::findBoolVariableSatVar(const std::string& name) const {
    auto it = boolVarSatVars_.find(name);
    if (it == boolVarSatVars_.end()) return std::nullopt;
    return it->second;
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
    records_.push_back({lit.var, theory, true, expr,
                        LinearAtomPayload{lhs, rel, RealValue::fromMpq(rhs)}});
    satVarToIdx_[lit.var] = idx;
    if (expr != NullExpr) exprIdToIdxs_[expr].push_back(idx);  // iter-101 perf
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
    if (expr != NullExpr) exprIdToIdxs_[expr].push_back(idx);  // iter-101 perf
    polyLookup_[key] = idx;
    observeIfNeeded(lit.var);

    return lit;
}

bool TheoryAtomRegistry::findByExprId(ExprId expr, LinearFormKey& outLhs,
                                       Relation& outRel, mpq_class& outRhs) const {
    // iter-101 perf: O(1) index lookup instead of O(N) linear scan.
    auto it = exprIdToIdxs_.find(expr);
    if (it == exprIdToIdxs_.end()) return false;
    for (size_t idx : it->second) {
        const auto& rec = records_[idx];
        if (std::holds_alternative<LinearAtomPayload>(rec.payload)) {
            const auto& p = std::get<LinearAtomPayload>(rec.payload);
            auto rhsQ = p.rhs.tryAsRational();
            if (!rhsQ) return false;  // algebraic RHS: caller wants mpq
            outLhs = p.lhs;
            outRel = p.rel;
            outRhs = *rhsQ;
            return true;
        }
    }
    return false;
}

// iter-50: lookup the SAT var for an arbitrary theory atom by ExprId.
// Used by NiaSolver::stageFarkasOr when constructing a narrow conflict
// for the UNSAT-emit path: each Farkas branch's `originalAnd` ExprId
// gets resolved to its SatVar so the conflict clause covers ALL
// branches (proxied or unproxied), not just the Tseitin proxies.
std::optional<SatVar>
TheoryAtomRegistry::findSatVarByExprId(ExprId expr) const {
    // iter-101 perf: O(1) index lookup instead of O(N) linear scan.
    auto it = exprIdToIdxs_.find(expr);
    if (it == exprIdToIdxs_.end() || it->second.empty()) return std::nullopt;
    return records_[it->second.front()].satVar;
}

const TheoryAtomRecord* TheoryAtomRegistry::findBySatVar(SatVar v) const {
    auto it = satVarToIdx_.find(v);
    if (it != satVarToIdx_.end()) {
        return &records_[it->second];
    }
    return nullptr;
}

std::vector<SatVar> TheoryAtomRegistry::linearAtomVars() const {
    std::vector<SatVar> out;
    for (const auto& rec : records_) {
        if (std::holds_alternative<LinearAtomPayload>(rec.payload)) {
            out.push_back(rec.satVar);
        }
    }
    return out;
}

std::vector<SatVar> TheoryAtomRegistry::allAtomVars() const {
    std::vector<SatVar> out;
    out.reserve(records_.size());
    for (const auto& rec : records_) out.push_back(rec.satVar);
    return out;
}

size_t TheoryAtomRegistry::numAtomVars() const { return records_.size(); }

long g_sharedEqAtomsCreated = 0;  // XOLVER_COMB_DIAG counter (read in TheoryManager.cpp)

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
    ++g_sharedEqAtomsCreated;

    size_t idx = records_.size();
    records_.push_back({lit.var, TheoryId::Combination, true, expr,
                        SharedEqualityPayload{a, b}});
    satVarToIdx_[lit.var] = idx;
    if (expr != NullExpr) exprIdToIdxs_[expr].push_back(idx);  // iter-101 perf
    sharedEqLookup_[key] = idx;
    observeIfNeeded(lit.var);

    // Nelson-Oppen default arrangement: prefer DISEQUAL for fresh interface
    // atoms (sound — phase only; see setDefaultSharedEqDisequal).
    if (defaultSharedEqDisequal_ && sat_) sat_->setDefaultPhase(lit.var, false);

    return lit;
}

SatLit TheoryAtomRegistry::getOrCreateEufEqualityAtom(ExprId lhs, ExprId rhs) {
    assert(sat_ != nullptr && registrar_ != nullptr);

    // Canonical key: min(lhs,rhs), max(lhs,rhs). The EUF solver treats Eq(a,b)
    // and Eq(b,a) identically, so they must share one SAT var.
    ExprId lo = lhs < rhs ? lhs : rhs;
    ExprId hi = lhs < rhs ? rhs : lhs;
    uint64_t key = (static_cast<uint64_t>(lo) << 32) | static_cast<uint64_t>(hi);

    auto it = eufEqLookup_.find(key);
    if (it != eufEqLookup_.end()) {
        const auto& rec = records_[it->second];
        return SatLit::positive(rec.satVar);
    }

    ExprId synthetic = nextSyntheticExprId_++;
    SatLit lit = registrar_->registerDynamicAtom(synthetic, TheoryId::EUF);

    size_t idx = records_.size();
    records_.push_back({lit.var, TheoryId::EUF, true, synthetic,
                        EufAtomPayload{lo, hi, Relation::Eq, EufAtomKind::Equality}});
    satVarToIdx_[lit.var] = idx;
    eufEqLookup_[key] = idx;
    observeIfNeeded(lit.var);

    return lit;
}

} // namespace xolver
