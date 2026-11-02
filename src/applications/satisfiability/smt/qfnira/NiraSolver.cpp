#include "applications/satisfiability/smt/qfnira/NiraSolver.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/linear/LinearAtomManager.h"
#include "algebra/linear/LinearExpr.h"
#include "search/nra/core/CdcacSolver.h"
#include "ir/NativeTerms.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <functional>
#include <iostream>

namespace xolver {

namespace {
std::optional<std::pair<LinearFormKey, mpq_class>> polyToLinearForm(
    const PolynomialKernel* kernel, PolyId poly);

// Closed singleton intervals are equalities too. Preserve all participating
// literals in the caller's explanation when using these substitutions.
template<class Assignments>
std::unordered_map<std::string, mpq_class> fixedLinearValues(
    const Assignments& assignments, const std::vector<ActiveLinearConstraint>* context) {
    struct Bounds { std::optional<mpq_class> lower, upper; };
    std::unordered_map<std::string, Bounds> bounds;
    auto collect = [&](const LinearAtomPayload& p) {
        if (p.lhs.terms.size() != 1) return;
        const auto& [name, coefficient] = p.lhs.terms.front();
        const auto rhs = p.rhs.tryAsRational();
        if (!rhs || coefficient == 0) return;
        const mpq_class value = *rhs / coefficient;
        auto& b = bounds[name];
        const bool lower = p.rel == Relation::Eq ||
            (coefficient > 0 ? p.rel == Relation::Geq : p.rel == Relation::Leq);
        const bool upper = p.rel == Relation::Eq ||
            (coefficient > 0 ? p.rel == Relation::Leq : p.rel == Relation::Geq);
        if (lower && (!b.lower || value > *b.lower)) b.lower = value;
        if (upper && (!b.upper || value < *b.upper)) b.upper = value;
    };
    for (const auto& a : assignments)
        if (auto* p = std::get_if<LinearAtomPayload>(&a.atom.payload)) collect(*p);
    if (context) for (const auto& a : *context) collect(a.payload);
    std::unordered_map<std::string, mpq_class> result;
    for (const auto& [name, b] : bounds)
        if (b.lower && b.upper && *b.lower == *b.upper) result.emplace(name, *b.lower);
    return result;
}
} // namespace

NiraSolver::NiraSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)) {
    if (kernel_) {
        converter_ = std::make_unique<PolynomialConverter>(*kernel_);
    }
}

NiraSolver::~NiraSolver() = default;

void NiraSolver::assertLit(const TheoryAtomRecord& atom, bool value,
                           int level, SatLit assertedLit) {
    auto effective = atom;
    if (!value) {
        if (auto* p = std::get_if<PolynomialAtomPayload>(&effective.payload))
            p->rel = negateRelation(p->rel);
        if (auto* p = std::get_if<LinearAtomPayload>(&effective.payload))
            p->rel = negateRelation(p->rel);
    }
    ArithSolverBase::assertLit(effective, true, level, assertedLit);
}

void NiraSolver::onPush() {
    gsRelax_.push();
}

void NiraSolver::onPop(uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) {
        gsRelax_.pop();
    }
}

void NiraSolver::onBacktrack(int targetLevel) {
    // Base already rolled back the trail; sync the relaxation simplex.
    gsRelax_.backtrackToLevel(targetLevel);
}

TheoryCheckResult NiraSolver::check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    currentModel_.reset();
    // Check if there are any active polynomial constraints
    bool hasPoly = false;
    for (const auto& a : trail()) {
        if (a.value && std::holds_alternative<PolynomialAtomPayload>(a.atom.payload)) {
            hasPoly = true;
            break;
        }
    }

    // If there are no polynomial obligations, NiraSolver has nothing to do.
    // Linear obligations are handled by LiraSolver (registered for QF_NIRA).
    if (!hasPoly) {
        return TheoryCheckResult::consistent();
    }

    // Simplify polynomial obligations under exact, explained linear facts.
    // A residual linear obligation belongs to the existing LIRA engine; it
    // must not be independently declared satisfiable by a nonlinear engine.
    if (kernel_) {
        const auto fixedValues = fixedLinearValues(trail(), activeLinearContext_);
        bool allLinear = true;
        for (const auto& a : trail()) {
            const auto* payload = std::get_if<PolynomialAtomPayload>(&a.atom.payload);
            if (!payload) continue;
            const auto rhs = payload->rhs.tryAsRational();
            if (!rhs) return TheoryCheckResult::unknown("NIRA: algebraic polynomial rhs");
            PolyId current = kernel_->sub(payload->poly, kernel_->mkConst(*rhs));
            for (const auto& [name, value] : fixedValues) {
                if (auto variable = kernel_->findVar(name))
                    if (auto substituted = kernel_->substituteRational(current, *variable, value))
                        current = *substituted;
            }
            if (kernel_->isConstant(current)) {
                const auto value = kernel_->toConstant(current);
                const bool holds = payload->rel == Relation::Eq ? value == 0 :
                    payload->rel == Relation::Neq ? value != 0 :
                    payload->rel == Relation::Lt ? value < 0 :
                    payload->rel == Relation::Leq ? value <= 0 :
                    payload->rel == Relation::Gt ? value > 0 : value >= 0;
                if (!holds)
                    return TheoryCheckResult::mkConflict(TheoryConflict{allActiveReasons()});
                continue;
            }
            const auto linear = polyToLinearForm(kernel_.get(), current);
            if (!linear) { allLinear = false; continue; }
            bool active = false;
            if (activeLinearContext_) for (const auto& fact : *activeLinearContext_) {
                if (fact.payload.lhs == linear->first &&
                    fact.payload.rel == payload->rel &&
                    fact.payload.rhs.tryAsRational() == std::optional<mpq_class>(linear->second)) {
                    active = true;
                    break;
                }
            }
            if (!active) {
                if (!registry_)
                    return TheoryCheckResult::unknown("NIRA: linear residual needs registry");
                auto reasons = allActiveReasons();
                const auto consequence = registry_->getOrCreateLinearBoundAtom(
                    linear->first, payload->rel, linear->second, TheoryId::LIRA);
                for (auto& reason : reasons) reason = reason.negated();
                reasons.push_back(consequence);
                return TheoryCheckResult::mkLemma(
                    TheoryLemma{std::move(reasons), LemmaKind::Entailment});
            }
        }
        if (allLinear) return TheoryCheckResult::consistent();
    }

    // --- Pure-subproblem delegation (cheap; runs at Full effort).
    // If, after fixed-value substitution, every remaining polynomial
    // constraint involves only real variables, route them through NRA's
    // CDCAC engine directly instead of trying bounded integer enumeration.
    if (effort == TheoryEffort::Full) {
        auto pure = checkPureSubproblems(lemmaDb);
        if (pure.kind == TheoryCheckResult::Kind::Consistent) return pure;
        if (pure.kind == TheoryCheckResult::Kind::Conflict)   return pure;
        // Otherwise (Unknown — mixed int/real polys remain) fall through.
    }

    // --- Full effort: bounded-complete enumeration ---
    if (effort == TheoryEffort::Full) {
        auto r = checkBoundedComplete(lemmaDb);
        if (r.kind == TheoryCheckResult::Kind::Consistent) return r;
        if (r.kind == TheoryCheckResult::Kind::Conflict) return r;
        if (r.kind == TheoryCheckResult::Kind::Unknown && !r.reason.empty()) {
            return TheoryCheckResult::unknown("NIRA: bounded-complete failed -> " + r.reason);
        }
    }

    // At Standard effort with polynomial payload but no immediate conflict:
    // we cannot conclude Consistent without Full effort enumeration.
    // Return Unknown so the SAT solver continues searching.
    return TheoryCheckResult::unknown("NIRA: polynomial payload needs Full effort");
}

namespace {
// Forward declaration; the body is in the anonymous namespace further down.
bool isIntegerVar(const NativeTerms* nativeTerms, const std::string& name);
} // namespace

TheoryCheckResult NiraSolver::checkPureSubproblems(TheoryLemmaStorage& /*lemmaDb*/) {
    if (!nativeTerms_ || !kernel_)
        return TheoryCheckResult::unknown("NIRA: pure delegation requires terms and kernel");
    const auto fixedValues = fixedLinearValues(trail(), activeLinearContext_);
    CdcacSolver residual(kernel_.get());
    for (const auto& a : trail()) {
        const auto* p = std::get_if<PolynomialAtomPayload>(&a.atom.payload);
        if (!p) continue;
        const auto rhs = p->rhs.tryAsRational();
        if (!rhs) return TheoryCheckResult::unknown("NIRA: algebraic polynomial rhs");
        auto current = kernel_->sub(p->poly, kernel_->mkConst(*rhs));
        for (const auto& [name, value] : fixedValues)
            if (auto variable = kernel_->findVar(name))
                if (auto sub = kernel_->substituteRational(current, *variable, value)) current = *sub;
        for (const auto& name : kernel_->variables(current))
            if (isIntegerVar(nativeTerms_, name))
                return TheoryCheckResult::unknown("NIRA: mixed integer/real residual");
        residual.assertConstraint(current, p->rel, a.lit, a.level);
    }
    // Linear and polynomial witnesses must agree. An unfixed integer coupled
    // to a real variable cannot be dropped from a delegated real problem.
    bool forwardable = true;
    auto forward = [&](const LinearAtomPayload& p, SatLit reason) {
        const auto rhs = p.rhs.tryAsRational();
        if (!rhs) { forwardable = false; return; }
        auto poly = kernel_->mkConst(-*rhs);
        bool real = false, unfixedInt = false;
        for (const auto& [name, coefficient] : p.lhs.terms) {
            if (coefficient == 0) continue;
            if (auto it = fixedValues.find(name); it != fixedValues.end()) {
                poly = kernel_->add(poly, kernel_->mkConst(coefficient * it->second));
            } else if (isIntegerVar(nativeTerms_, name)) {
                unfixedInt = true;
            } else {
                real = true;
                poly = kernel_->add(poly, kernel_->mul(kernel_->mkConst(coefficient),
                    kernel_->mkVar(kernel_->getOrCreateVar(name))));
            }
        }
        if (unfixedInt) {
            if (real) forwardable = false;
            return; // Independent pure-integer obligations remain with LIRA.
        }
        residual.assertConstraint(poly, p.rel, reason, 0);
    };
    for (const auto& a : trail())
        if (const auto* p = std::get_if<LinearAtomPayload>(&a.atom.payload)) forward(*p, a.lit);
    if (activeLinearContext_)
        for (const auto& fact : *activeLinearContext_) forward(fact.payload, fact.reasonLit);
    if (!forwardable)
        return TheoryCheckResult::unknown("NIRA: residual couples unfixed integer and real values");
    const auto result = residual.check();
    if (result.kind == TheoryCheckResult::Kind::Conflict)
        return TheoryCheckResult::mkConflict(TheoryConflict{allActiveReasons()});
    if (result.kind != TheoryCheckResult::Kind::Consistent) return result;
    const auto sample = residual.getModel();
    if (!sample) return TheoryCheckResult::unknown("NIRA: no joint residual witness");
    TheoryModel model;
    for (const auto& [name, value] : fixedValues) {
        model.numericAssignments.emplace(name, RealValue::fromMpq(value));
        model.assignments.emplace(name, value.get_str());
    }
    for (size_t i = 0; i < sample->varOrder.size(); ++i) {
        const std::string name(kernel_->varName(sample->varOrder[i]));
        const auto value = residual.sampleValueToRealValue(sample->values[i]);
        model.numericAssignments.insert_or_assign(name, value);
        model.assignments.insert_or_assign(name,
            value.isRational() ? value.asRational().get_str() : value.toSmtLib2());
    }
    currentModel_ = std::move(model);
    return result;
}

TheoryCheckResult NiraSolver::checkRelaxationAndValidate(TheoryLemmaStorage& /*lemmaDb*/) {
    return TheoryCheckResult::unknown("NIRA: relaxation+validate not yet implemented");
}

namespace {

bool isIntegerVar(const NativeTerms* nativeTerms, const std::string& name) {
    if (!nativeTerms) return false;
    for (size_t i = 0; i < nativeTerms->size(); ++i) {
        ExprId eid = static_cast<ExprId>(i);
        const auto& expr = nativeTerms->get(eid);
        if (expr.kind == Kind::Variable) {
            if (std::holds_alternative<std::string>(expr.payload.value)) {
                if (std::get<std::string>(expr.payload.value) == name) {
                    return expr.sort == nativeTerms->intSortId();
                }
            }
        }
    }
    return false;
}

// Try to convert a substituted polynomial to a linear form.
// Returns nullopt if the polynomial is not linear.
std::optional<std::pair<LinearFormKey, mpq_class>> polyToLinearForm(
    const PolynomialKernel* kernel, PolyId poly) {
    auto termsOpt = kernel->terms(poly);
    if (!termsOpt) return std::nullopt;

    LinearFormKey lhs;
    mpq_class rhs = 0;

    for (const auto& term : *termsOpt) {
        if (term.powers.empty()) {
            rhs -= mpq_class(term.coefficient);
        } else if (term.powers.size() == 1 && term.powers[0].second == 1) {
            auto varName = kernel->varName(term.powers[0].first);
            lhs.terms.push_back({std::string(varName), mpq_class(term.coefficient)});
        } else {
            return std::nullopt; // Non-linear
        }
    }

    std::sort(lhs.terms.begin(), lhs.terms.end(),
              [](auto& a, auto& b) { return a.first < b.first; });
    return std::make_pair(lhs, rhs);
}

} // anonymous namespace

// Check all polynomial and linear obligations under one integer assignment.
NiraSolver::AssignmentCheckResult NiraSolver::checkAssignmentWithRealSolver(
    const std::vector<ActiveAssignment>& assignments,
    const std::vector<ActiveLinearConstraint>* linearCtx,
    const std::unordered_map<std::string, mpq_class>& fixedValues,
    PolynomialKernel* kernel, TheoryModel* model) {
    // Every integer in this residual was assigned by the bounded enumerator.
    // Decide the remaining real conjunction together, including disequalities.
    CdcacSolver residual(kernel);
    auto linear = [&](const LinearAtomPayload& p) {
        const auto rhs = p.rhs.tryAsRational();
        if (!rhs) return false;
        auto poly = kernel->mkConst(-*rhs);
        for (const auto& [name, coefficient] : p.lhs.terms) {
            if (coefficient == 0) continue;
            const auto it = fixedValues.find(name);
            const auto term = it != fixedValues.end() ? kernel->mkConst(coefficient * it->second)
                : kernel->mul(kernel->mkConst(coefficient),
                    kernel->mkVar(kernel->getOrCreateVar(name)));
            poly = kernel->add(poly, term);
        }
        residual.assertConstraint(poly, p.rel, {}, 0);
        return true;
    };
    for (const auto& a : assignments) {
        if (const auto* p = std::get_if<LinearAtomPayload>(&a.atom.payload)) {
            if (!linear(*p)) return AssignmentCheckResult::Unknown;
        } else if (const auto* p = std::get_if<PolynomialAtomPayload>(&a.atom.payload)) {
            const auto rhs = p->rhs.tryAsRational();
            if (!rhs) return AssignmentCheckResult::Unknown;
            auto poly = kernel->sub(p->poly, kernel->mkConst(*rhs));
            for (const auto& [name, value] : fixedValues)
                if (const auto variable = kernel->findVar(name))
                    if (const auto sub = kernel->substituteRational(poly, *variable, value)) poly = *sub;
            residual.assertConstraint(poly, p->rel, {}, 0);
        }
    }
    if (linearCtx) for (const auto& a : *linearCtx)
        if (!linear(a.payload)) return AssignmentCheckResult::Unknown;
    const auto result = residual.check();
    if (result.kind == TheoryCheckResult::Kind::Conflict) return AssignmentCheckResult::Unsat;
    if (result.kind != TheoryCheckResult::Kind::Consistent) return AssignmentCheckResult::Unknown;
    const auto sample = residual.getModel();
    if (!sample) return AssignmentCheckResult::Unknown;
    for (const auto& [name, value] : fixedValues) {
        model->numericAssignments.emplace(name, RealValue::fromMpq(value));
        model->assignments.emplace(name, value.get_str());
    }
    for (size_t i = 0; i < sample->varOrder.size(); ++i) {
        const std::string name(kernel->varName(sample->varOrder[i]));
        const auto value = residual.sampleValueToRealValue(sample->values[i]);
        model->numericAssignments.insert_or_assign(name, value);
        model->assignments.insert_or_assign(name,
            value.isRational() ? value.asRational().get_str() : value.toSmtLib2());
    }
    return AssignmentCheckResult::Sat;
}

TheoryCheckResult NiraSolver::checkBoundedComplete(TheoryLemmaStorage& /*lemmaDb*/) {
    if (!nativeTerms_ || !kernel_) {
        return TheoryCheckResult::unknown("NIRA: missing NativeTerms or PolynomialKernel");
    }

    // Step 1: Extract integer variable bounds from single-variable linear constraints
    struct BoundInfo {
        std::optional<mpz_class> lower;
        std::optional<mpz_class> upper;
    };
    std::unordered_map<std::string, BoundInfo> bounds;

    // 1a: from active NIRA linear atoms
    for (const auto& a : trail()) {
        if (!a.value) continue;
        if (!std::holds_alternative<LinearAtomPayload>(a.atom.payload)) continue;

        const auto& p = std::get<LinearAtomPayload>(a.atom.payload);
        if (p.lhs.terms.size() != 1) continue;

        const auto& [name, coeff] = p.lhs.terms[0];
        if (!isIntegerVar(nativeTerms_, name)) continue;

        mpq_class rawBound = p.rhs.asRational() / coeff;
        if (rawBound.get_den() != 1) continue;

        mpz_class boundVal = rawBound.get_num();
        bool pos = coeff > 0;

        switch (p.rel) {
            case Relation::Eq:
                bounds[name].lower = boundVal;
                bounds[name].upper = boundVal;
                break;
            case Relation::Leq:
                if (pos) bounds[name].upper = boundVal;
                else     bounds[name].lower = boundVal;
                break;
            case Relation::Geq:
                if (pos) bounds[name].lower = boundVal;
                else     bounds[name].upper = boundVal;
                break;
            case Relation::Lt:
                if (pos) bounds[name].upper = boundVal - 1;
                else     bounds[name].lower = boundVal + 1;
                break;
            case Relation::Gt:
                if (pos) bounds[name].lower = boundVal + 1;
                else     bounds[name].upper = boundVal - 1;
                break;
            default: break;
        }
    }

    // 1b: from active LIRA linear atoms (via ActiveLinearContext)
    if (activeLinearContext_) {
        for (const auto& alc : *activeLinearContext_) {
            const auto& p = alc.payload;
            if (p.lhs.terms.size() != 1) continue;

            const auto& [name, coeff] = p.lhs.terms[0];
            if (!isIntegerVar(nativeTerms_, name)) continue;

            mpq_class rawBound = p.rhs.asRational() / coeff;
            if (rawBound.get_den() != 1) continue;

            mpz_class boundVal = rawBound.get_num();
            bool pos = coeff > 0;

            switch (p.rel) {
                case Relation::Eq:
                    bounds[name].lower = boundVal;
                    bounds[name].upper = boundVal;
                    break;
                case Relation::Leq:
                    if (pos) bounds[name].upper = boundVal;
                    else     bounds[name].lower = boundVal;
                    break;
                case Relation::Geq:
                    if (pos) bounds[name].lower = boundVal;
                    else     bounds[name].upper = boundVal;
                    break;
                case Relation::Lt:
                    if (pos) bounds[name].upper = boundVal - 1;
                    else     bounds[name].lower = boundVal + 1;
                    break;
                case Relation::Gt:
                    if (pos) bounds[name].lower = boundVal + 1;
                    else     bounds[name].upper = boundVal - 1;
                    break;
                default: break;
            }
        }
    }

    // Step 2: Identify if there are any polynomial constraints at all.
    bool hasPolynomialPayload = false;
    for (const auto& a : trail()) {
        if (!a.value) continue;
        if (std::holds_alternative<PolynomialAtomPayload>(a.atom.payload)) {
            hasPolynomialPayload = true;
            break;
        }
    }
    if (!hasPolynomialPayload) {
        return TheoryCheckResult::consistent();
    }

    // Step 2b: Identify integer variables appearing in polynomial constraints
    std::unordered_set<std::string> polyIntVars;
    for (const auto& a : trail()) {
        if (!a.value) continue;
        if (!std::holds_alternative<PolynomialAtomPayload>(a.atom.payload)) continue;

        const auto& p = std::get<PolynomialAtomPayload>(a.atom.payload);
        auto vars = kernel_->variables(p.poly);
        for (const auto& v : vars) {
            if (isIntegerVar(nativeTerms_, v)) polyIntVars.insert(v);
        }
    }

    // Step 2c: Also consider integer variables from linear constraints
    // (they may bound real variables even if not appearing in polynomials).
    std::unordered_set<std::string> allIntVars = polyIntVars;
    auto collectIntVarsFromLinear = [&](const LinearAtomPayload& p) {
        for (const auto& [name, coeff] : p.lhs.terms) {
            (void)coeff;
            if (isIntegerVar(nativeTerms_, name)) allIntVars.insert(name);
        }
    };
    for (const auto& a : trail()) {
        if (!a.value) continue;
        if (!std::holds_alternative<LinearAtomPayload>(a.atom.payload)) continue;
        collectIntVarsFromLinear(std::get<LinearAtomPayload>(a.atom.payload));
    }
    if (activeLinearContext_) {
        for (const auto& alc : *activeLinearContext_) {
            collectIntVarsFromLinear(alc.payload);
        }
    }

    if (allIntVars.empty()) {
        return TheoryCheckResult::unknown(
            "NIRA: no integer variables at all; NRA delegation not implemented");
    }

    // Step 3: Separate bounded vs unbounded integer variables
    std::vector<std::string> enumVars;   // bounded variables to enumerate
    std::vector<std::string> unboundedVars;
    for (const auto& name : allIntVars) {
        auto it = bounds.find(name);
        if (it != bounds.end() && it->second.lower && it->second.upper) {
            enumVars.push_back(name);
        } else {
            unboundedVars.push_back(name);
        }
    }

    // Heuristic SAT-search for half-bounded integer variables: when an int
    // var has exactly one bound, pin the trial value to that bound (so the
    // bound is realized) and add it to the enumeration set as a single-point
    // range. This is sound for SAT (the value really does satisfy the bound
    // and any satisfying combination becomes a model) but the resulting
    // enumeration is no longer exhaustive — if every pinned trial fails we
    // must NOT emit UNSAT, only Unknown. Catches SAT-side patterns like
    //     i > 0 ∧ r > 0 ∧ i*r > 0           (nira_004)
    //     i ≥ 1 ∧ r ≥ 0 ∧ i*r ≤ 1           (nira_011)
    // where the lower-bound corner — i = 1, paired with the simplex check on
    // the residual real-only fragment — is already a witness.
    bool usedHeuristicPin = false;
    for (const auto& name : unboundedVars) {
        auto it = bounds.find(name);
        if (it == bounds.end()) {
            usedHeuristicPin = true;  // truly free var, can't pin
            continue;
        }
        BoundInfo& bi = it->second;
        if (bi.lower && !bi.upper) {
            bi.upper = bi.lower;  // pin to lower
            enumVars.push_back(name);
            usedHeuristicPin = true;
        } else if (bi.upper && !bi.lower) {
            bi.lower = bi.upper;  // pin to upper
            enumVars.push_back(name);
            usedHeuristicPin = true;
        } else {
            usedHeuristicPin = true;
        }
    }

    if (enumVars.empty() || enumVars.size() != allIntVars.size()) {
        // No bounded variables to enumerate; cannot make progress.
        return TheoryCheckResult::unknown("NIRA: unbounded integer variable(s)");
    }

    std::sort(enumVars.begin(), enumVars.end());
    std::unordered_map<std::string, mpq_class> fixedValues;
    bool sawUnknown = false;
    WorkBudget deadline(0);

    std::function<bool(int)> enumerate = [&](int idx) -> bool {
        deadline.tick();
        if (idx == (int)enumVars.size()) {
            TheoryModel witness;
            auto r = NiraSolver::checkAssignmentWithRealSolver(
                trail(), activeLinearContext_, fixedValues, kernel_.get(), &witness);
            if (r == AssignmentCheckResult::Sat) {
                currentModel_ = std::move(witness);
                return true;
            }
            if (r == AssignmentCheckResult::Unknown) {
                sawUnknown = true;
            }
            return false;
        }

        const std::string& varName = enumVars[idx];
        mpz_class lo = *bounds[varName].lower;
        mpz_class hi = *bounds[varName].upper;

        if (lo > hi) return false;

        for (mpz_class val = lo; val <= hi; ++val) {
            fixedValues[varName] = mpq_class(val);
            if (enumerate(idx + 1)) return true;
        }
        fixedValues.erase(varName);
        return false;
    };

    if (enumerate(0)) {
        return TheoryCheckResult::consistent();
    }

    if (sawUnknown) {
        return TheoryCheckResult::unknown(
            "NIRA: bounded-complete enumeration hit non-linear real residual");
    }

    if (usedHeuristicPin) {
        // We pinned at least one unbounded var to a single value; an
        // exhaustive UNSAT proof requires every possible integer value to
        // have been refuted. Return Unknown — the SAT solver will continue.
        return TheoryCheckResult::unknown(
            "NIRA: heuristic pin exhausted without SAT, true range unexplored");
    }

    // Bounds and linear side constraints are part of this refutation too.
    return TheoryCheckResult::mkConflict(TheoryConflict{allActiveReasons()});
}

bool NiraSolver::validateOriginalConstraints() const {
    return true;
}

void NiraSolver::onReset() {
    // Base clears the trail; reset the relaxation simplex here.
    gsRelax_.reset();
    currentModel_.reset();
}

void NiraSolver::setRegistry(TheoryAtomRegistry* reg) {
    registry_ = reg;
}

// setNativeTerms now uses the ArithSolverBase default (2026-06-04).

std::optional<TheorySolver::TheoryModel> NiraSolver::getModel() const {
    return currentModel_;
}

std::vector<SatLit> NiraSolver::allActiveReasons() const {
    std::vector<SatLit> reasons;
    for (const auto& a : trail()) {
        reasons.push_back(a.lit);
    }
    if (activeLinearContext_)
        for (const auto& fact : *activeLinearContext_)
            if (std::find(reasons.begin(), reasons.end(), fact.reasonLit) == reasons.end())
                reasons.push_back(fact.reasonLit);
    return reasons;
}

} // namespace xolver
