#include "theory/arith/nra/NraSolver.h"
#include "theory/arith/Reasoner.h"
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/presolve/Presolve.h"
#include "theory/arith/poly/RationalPolynomial.h"
#include <iostream>

namespace nlcolver {

NraSolver::NraSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)),
      converter_(std::make_unique<PolynomialConverter>(*kernel_)),
      engine_(kernel_.get()) {
    // Phase 2 reasoner pipeline: presolve fixpoint, then CDCAC.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.presolve",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stagePresolve(db, e); }));
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.cdcac",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCdcac(db, e); }));
}

void NraSolver::onPush() {
    scopeStack_.push_back(activeLits_.size());
    engine_.push();
}

void NraSolver::onPop(uint32_t n) {
    for (uint32_t i = 0; i < n && !scopeStack_.empty(); ++i) {
        size_t targetSize = scopeStack_.back();
        scopeStack_.pop_back();
        activeLits_.resize(targetSize);
    }
    trail_.clear();  // V5: rebuild trail from activeLits on next backtrack
    activeSet_.rebuildFromActive(activeLits_, [](const auto& lit) { return lit; });
    presolveConstraints_.resize(activeLits_.size());
    engine_.pop(n);
}

void NraSolver::onReset() {
    engine_.reset();
    activeLits_.clear();
    trail_.clear();
    presolveConstraints_.clear();
    scopeStack_.clear();
    activeSet_.reset();
    interfaceEqualities_.clear();
    interfaceDisequalities_.clear();
}

void NraSolver::assertLit(const TheoryAtomRecord& atom, bool value,
                          int level, SatLit reason) {
    // Facade-level dedup: same polarity already active → ignore.
    // Opposite polarity is left to the engine's defense-in-depth check.
    if (activeSet_.contains(reason)) {
        return;
    }
    activeSet_.insert(reason);

    size_t oldSize = activeLits_.size();
    activeLits_.push_back(reason);
    trail_.push_back({level, oldSize});

    const auto* payload = std::get_if<PolynomialAtomPayload>(&atom.payload);
    if (!payload) {
        // Payload mismatch is an internal routing error, NOT a theory conflict.
        // Engine will see this as unsupported and return Unknown.
        presolveConstraints_.push_back({NullPoly, Relation::Eq, reason});  // keep aligned
        engine_.reset();
        return;
    }

    Relation rel = value ? payload->rel : negateRelation(payload->rel);
    // Presolve sees the constraint in `p rel 0` form (subtract rhs if present).
    PolyId diff = payload->poly;
    if (payload->rhs != 0) diff = kernel_->sub(payload->poly, kernel_->mkConst(payload->rhs));
    presolveConstraints_.push_back({diff, rel, reason});
    engine_.assertConstraint(payload->poly, rel, reason, level);
}

void NraSolver::onBacktrack(int level) {
    while (!trail_.empty() && trail_.back().level > level) {
        activeLits_.resize(trail_.back().activeSizeBefore);
        trail_.pop_back();
    }
    activeSet_.rebuildFromActive(activeLits_, [](const auto& lit) { return lit; });
    presolveConstraints_.resize(activeLits_.size());
    engine_.backtrack(level);
    auto ieIt = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceEqualities_.erase(ieIt, interfaceEqualities_.end());
    auto idIt = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceDisequalities_.erase(idIt, interfaceDisequalities_.end());
}

// Stage 1: theory-check presolve fixpoint (Caps. 1–5, 7, with Real domain).
// May return a Conflict (UNSAT direction) via exact linear/sign reasoning,
// or a Lemma; it never returns SAT directly. nullopt → continue to CDCAC.
std::optional<TheoryCheckResult> NraSolver::stagePresolve(TheoryLemmaStorage& /*lemmaDb*/,
                                                          TheoryEffort /*effort*/) {
    PresolveEngine presolve(kernel_.get(), /*integerDomain=*/false);
    bool feasible = true;
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;  // non-polynomial placeholder
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) { feasible = false; break; }
        presolve.addAtom(*rp, c.rel, c.reason);
    }
    if (feasible) {
        auto pr = presolve.run();
        if (pr.kind == PresolveResult::Kind::Conflict)
            return TheoryCheckResult::mkConflict(pr.conflict);
        if (pr.kind == PresolveResult::Kind::Lemma)
            return TheoryCheckResult::mkLemma(pr.lemma);
    }
    return std::nullopt;
}

// Stage 2: the CDCAC engine. Always yields a definite verdict.
std::optional<TheoryCheckResult> NraSolver::stageCdcac(TheoryLemmaStorage& /*lemmaDb*/,
                                                       TheoryEffort /*effort*/) {
    return engine_.check();
}

TheoryCheckResult NraSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {
    if (!sharedTermRegistry_ || !coreIr_ || !converter_)
        return TheoryCheckResult::consistent();
    const auto* stA = sharedTermRegistry_->get(a);
    const auto* stB = sharedTermRegistry_->get(b);
    if (!stA || !stB) return TheoryCheckResult::consistent();

    auto cc = converter_->convertConstraint(stA->coreExpr, stB->coreExpr,
                                            Relation::Eq, *coreIr_);
    if (cc.status == PolyConstraintStatus::Tautology)
        return TheoryCheckResult::consistent();
    if (cc.status == PolyConstraintStatus::Conflict)
        return TheoryCheckResult::mkConflict(TheoryConflict{{reason}});
    if (!cc.isConstraint())
        return TheoryCheckResult::consistent();

    engine_.assertConstraint(cc.diff, Relation::Eq, reason, level);
    interfaceEqualities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

TheoryCheckResult NraSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {
    if (!sharedTermRegistry_ || !coreIr_ || !converter_)
        return TheoryCheckResult::consistent();
    const auto* stA = sharedTermRegistry_->get(a);
    const auto* stB = sharedTermRegistry_->get(b);
    if (!stA || !stB) return TheoryCheckResult::consistent();

    auto cc = converter_->convertConstraint(stA->coreExpr, stB->coreExpr,
                                            Relation::Neq, *coreIr_);
    if (cc.status == PolyConstraintStatus::Tautology)
        return TheoryCheckResult::consistent();
    if (cc.status == PolyConstraintStatus::Conflict)
        return TheoryCheckResult::mkConflict(TheoryConflict{{reason}});
    if (!cc.isConstraint())
        return TheoryCheckResult::consistent();

    engine_.assertConstraint(cc.diff, Relation::Neq, reason, level);
    interfaceDisequalities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

std::vector<TheorySolver::SharedEqualityPropagation>
NraSolver::getDeducedSharedEqualities() {
    return {};
}

std::optional<TheorySolver::TheoryModel> NraSolver::getModel() const {
    auto sampleOpt = engine_.getModel();
    if (!sampleOpt) return std::nullopt;
    const auto& sample = *sampleOpt;

    TheoryModel model;
    for (size_t i = 0; i < sample.varOrder.size(); ++i) {
        VarId v = sample.varOrder[i];
        const auto& val = sample.values[i];
        std::string name(kernel_->varName(v));
        // Typed channel: exact RealValue (rational or algebraic).
        model.numericAssignments.insert({name, engine_.sampleValueToRealValue(val)});
        // Legacy string channel (retained during the funnel migration).
        std::string valueStr;
        if (val.kind == RealAlg::Kind::Rational) {
            valueStr = val.rational.get_str();
        } else {
            // AlgebraicRoot: strict representation with defining polynomial + isolating interval
            valueStr = engine_.formatAlgebraicRoot(val.root);
        }
        model.assignments[std::move(name)] = std::move(valueStr);
    }
    return model;
}

} // namespace nlcolver
