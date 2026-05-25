#include "theory/arith/nira/NiraSolver.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/arith/linear/LinearAtomManager.h"
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/nra/core/CdcacSolver.h"
#include "expr/ir.h"
#include <algorithm>
#include <functional>
#include <iostream>

namespace nlcolver {

NiraSolver::NiraSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)) {
    if (kernel_) {
        converter_ = std::make_unique<PolynomialConverter>(*kernel_);
    }
}

NiraSolver::~NiraSolver() = default;

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

    // --- Presolve: fixed-value substitution ---
    if (kernel_) {
        std::cerr << "[NIRA] check: hasPoly=" << hasPoly
                  << " activeLinearCtx=" << (activeLinearContext_ ? activeLinearContext_->size() : 0)
                  << "\n";
        std::unordered_map<std::string, mpq_class> fixedValues;

        // Step 1a: collect fixed values from active NIRA linear equalities
        for (const auto& a : trail()) {
            if (!std::holds_alternative<LinearAtomPayload>(a.atom.payload)) continue;
            if (!a.value) continue;

            const auto& payload = std::get<LinearAtomPayload>(a.atom.payload);
            if (payload.rel != Relation::Eq) continue;
            if (payload.lhs.terms.size() != 1) continue;

            const auto& term = payload.lhs.terms[0];
            if (term.second == 0) continue;
            auto rq = payload.rhs.tryAsRational();
            if (!rq) continue;
            fixedValues[term.first] = *rq / term.second;
        }

        // Step 1b: collect fixed values from active LIRA linear equalities
        if (activeLinearContext_) {
            for (const auto& alc : *activeLinearContext_) {
                const auto& p = alc.payload;
                if (p.rel != Relation::Eq) continue;
                if (p.lhs.terms.size() != 1) continue;

                const auto& term = p.lhs.terms[0];
                if (term.second == 0) continue;
                auto rq = p.rhs.tryAsRational();
                if (!rq) continue;
                fixedValues[term.first] = *rq / term.second;
            }
        }

        // Step 2: substitute into polynomial constraints
        for (const auto& a : trail()) {
            if (!std::holds_alternative<PolynomialAtomPayload>(a.atom.payload)) continue;
            if (!a.value) continue;

            const auto& payload = std::get<PolynomialAtomPayload>(a.atom.payload);
            PolyId current = payload.poly;

            for (const auto& [name, value] : fixedValues) {
                auto varIdOpt = kernel_->findVar(name);
                if (!varIdOpt) continue;
                auto substituted = kernel_->substituteRational(current, *varIdOpt, value);
                if (substituted) current = *substituted;
            }

            if (kernel_->isConstant(current)) {
                mpq_class val = kernel_->toConstant(current);
                bool satisfied = false;
                switch (payload.rel) {
                    case Relation::Eq:  satisfied = (val == 0); break;
                    case Relation::Neq: satisfied = (val != 0); break;
                    case Relation::Lt:  satisfied = (val < 0); break;
                    case Relation::Leq: satisfied = (val <= 0); break;
                    case Relation::Gt:  satisfied = (val > 0); break;
                    case Relation::Geq: satisfied = (val >= 0); break;
                }
                if (!satisfied) {
                    return TheoryCheckResult::mkConflict(TheoryConflict{{a.lit}});
                }
            }
        }
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
bool isIntegerVar(const CoreIr* coreIr, const std::string& name);
} // namespace

TheoryCheckResult NiraSolver::checkPureSubproblems(TheoryLemmaStorage& /*lemmaDb*/) {
    // After substituting fixed integer values into polynomial constraints,
    // some polynomials may collapse into pure-real form (no integer variables
    // remaining). For those, NIRA's bounded-complete enumeration over integer
    // assignments is the wrong tool — we just need NRA on the residual
    // polynomial system. Spin up a fresh CdcacSolver, push the surviving
    // real-only constraints, and forward its verdict.
    //
    // The path is needed for:
    //   * inputs that are pure-NRA in disguise (`r²=-1`, `2r²-3r+1=0`),
    //   * NIRA inputs whose integer variables vanish post-substitution
    //     (`r² ≥ 1 ∧ i ≤ 5`, where i is otherwise irrelevant).
    if (!coreIr_ || !kernel_) {
        return TheoryCheckResult::unknown(
            "NIRA: pure-subproblem delegation requires kernel and coreIr");
    }

    // Step 1: collect fixed-value substitutions (single-variable linear
    // equalities, from active NIRA atoms and the LIRA linear context).
    std::unordered_map<std::string, mpq_class> fixedValues;
    auto collectFixed = [&](const LinearAtomPayload& p) {
        if (p.rel != Relation::Eq) return;
        if (p.lhs.terms.size() != 1) return;
        const auto& [name, coeff] = p.lhs.terms[0];
        if (coeff == 0) return;
        auto rq = p.rhs.tryAsRational();
        if (!rq) return;
        fixedValues[name] = *rq / coeff;
    };
    for (const auto& a : trail()) {
        if (!a.value) continue;
        if (auto* p = std::get_if<LinearAtomPayload>(&a.atom.payload)) collectFixed(*p);
    }
    if (activeLinearContext_) {
        for (const auto& alc : *activeLinearContext_) collectFixed(alc.payload);
    }

    // Step 2: substitute into each polynomial constraint and classify.
    struct RealConstraint {
        PolyId poly;
        Relation rel;
        SatLit reason;
        int level;
    };
    std::vector<RealConstraint> realPolys;
    bool sawMixed = false;
    for (const auto& a : trail()) {
        if (!a.value) continue;
        if (!std::holds_alternative<PolynomialAtomPayload>(a.atom.payload)) continue;
        const auto& payload = std::get<PolynomialAtomPayload>(a.atom.payload);
        PolyId current = payload.poly;
        for (const auto& [name, value] : fixedValues) {
            auto varIdOpt = kernel_->findVar(name);
            if (!varIdOpt) continue;
            if (auto sub = kernel_->substituteRational(current, *varIdOpt, value)) {
                current = *sub;
            }
        }
        // Constant polynomials are already covered by check()'s presolve.
        if (kernel_->isConstant(current)) continue;

        bool hasInt = false;
        for (const auto& v : kernel_->variables(current)) {
            if (isIntegerVar(coreIr_, v)) { hasInt = true; break; }
        }
        if (hasInt) {
            sawMixed = true;
            continue;
        }
        realPolys.push_back({current, payload.rel, a.lit, a.level});
    }

    if (sawMixed) {
        return TheoryCheckResult::unknown("NIRA: mixed int/real polys remain");
    }

    if (realPolys.empty()) {
        return TheoryCheckResult::consistent();
    }

    // Step 3: delegate to a fresh CDCAC engine on the real-only residual.
    CdcacSolver cdcac(kernel_.get());
    for (const auto& rp : realPolys) {
        cdcac.assertConstraint(rp.poly, rp.rel, rp.reason, rp.level);
    }
    return cdcac.check();
}

TheoryCheckResult NiraSolver::checkRelaxationAndValidate(TheoryLemmaStorage& /*lemmaDb*/) {
    return TheoryCheckResult::unknown("NIRA: relaxation+validate not yet implemented");
}

namespace {

bool isIntegerVar(const CoreIr* coreIr, const std::string& name) {
    if (!coreIr) return false;
    for (size_t i = 0; i < coreIr->size(); ++i) {
        ExprId eid = static_cast<ExprId>(i);
        const auto& expr = coreIr->get(eid);
        if (expr.kind == Kind::Variable) {
            if (std::holds_alternative<std::string>(expr.payload.value)) {
                if (std::get<std::string>(expr.payload.value) == name) {
                    return expr.sort == coreIr->intSortId();
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

// Standalone enum for the free-function helper (avoids private member access).
enum class UvCheckResult { Sat, Unsat, Unknown };

// Check a univariate polynomial (after integer substitution) for satisfiability.
// Handles quadratics and odd-degree polynomials directly without NRA delegation.
static UvCheckResult checkUnivariatePoly(
    const PolynomialKernel* kernel, PolyId poly, Relation rel) {
    auto termsOpt = kernel->terms(poly);
    if (!termsOpt) return UvCheckResult::Unknown;

    // Identify the single variable and collect coefficients by degree.
    std::optional<VarId> varId;
    std::unordered_map<int, mpq_class> coeffsByDegree;
    for (const auto& term : *termsOpt) {
        if (term.powers.empty()) {
            coeffsByDegree[0] += mpq_class(term.coefficient);
        } else if (term.powers.size() == 1) {
            if (!varId) {
                varId = term.powers[0].first;
            } else if (*varId != term.powers[0].first) {
                return UvCheckResult::Unknown; // multivariate
            }
            coeffsByDegree[term.powers[0].second] += mpq_class(term.coefficient);
        } else {
            return UvCheckResult::Unknown; // multivariate
        }
    }

    if (!varId) {
        // Constant — should have been handled by caller.
        return UvCheckResult::Unknown;
    }

    // Determine degree.
    int degree = 0;
    for (const auto& [d, _] : coeffsByDegree) {
        if (d > degree) degree = d;
    }
    if (degree == 0) {
        return UvCheckResult::Unknown;
    }

    // For odd degree ≥ 1: polynomial goes to ±∞ on opposite sides,
    // so >0 and <0 are always satisfiable; =0 always has a real root.
    if (degree % 2 == 1) {
        switch (rel) {
            case Relation::Eq:
            case Relation::Neq:
            case Relation::Gt:
            case Relation::Lt:
                return UvCheckResult::Sat;
            case Relation::Geq:
            case Relation::Leq:
                // Touching zero is guaranteed for odd degree.
                return UvCheckResult::Sat;
        }
    }

    // Even degree: need more analysis.  For degree 2 we use discriminant.
    if (degree == 2) {
        mpq_class a = coeffsByDegree.count(2) ? coeffsByDegree[2] : mpq_class(0);
        mpq_class b = coeffsByDegree.count(1) ? coeffsByDegree[1] : mpq_class(0);
        mpq_class c = coeffsByDegree.count(0) ? coeffsByDegree[0] : mpq_class(0);

        if (a == 0) {
            // Degenerate to linear — should not reach here.
            return UvCheckResult::Unknown;
        }

        // Discriminant D = b² - 4ac
        mpq_class D = b * b - 4 * a * c;

        switch (rel) {
            case Relation::Eq:
                return (D >= 0) ? UvCheckResult::Sat : UvCheckResult::Unsat;
            case Relation::Neq:
                // Non-constant polynomial is non-zero almost everywhere.
                return UvCheckResult::Sat;
            case Relation::Gt:
                // p(x) > 0 for some x?  Unsat only if always negative.
                // Always negative: a < 0 and D < 0.
                if (a < 0 && D < 0) return UvCheckResult::Unsat;
                return UvCheckResult::Sat;
            case Relation::Lt:
                // p(x) < 0 for some x?  Unsat only if always positive.
                // Always positive: a > 0 and D < 0.
                if (a > 0 && D < 0) return UvCheckResult::Unsat;
                return UvCheckResult::Sat;
            case Relation::Geq:
                // p(x) ≥ 0 for some x?  Unsat only if always negative.
                if (a < 0 && D < 0) return UvCheckResult::Unsat;
                return UvCheckResult::Sat;
            case Relation::Leq:
                // p(x) ≤ 0 for some x?  Unsat only if always positive.
                if (a > 0 && D < 0) return UvCheckResult::Unsat;
                return UvCheckResult::Sat;
        }
    }

    // Even degree > 2: conservative.
    return UvCheckResult::Unknown;
}

} // anonymous namespace

// Check whether a single linear/polynomial assignment satisfies all constraints
// using a fresh GeneralSimplex instance.
NiraSolver::AssignmentCheckResult NiraSolver::checkAssignmentWithSimplex(
    const std::vector<ActiveAssignment>& activeAssignments,
    const std::vector<ActiveLinearConstraint>* linearCtx,
    const std::unordered_map<std::string, mpq_class>& fixedValues,
    PolynomialKernel* kernel) {

    GeneralSimplex gs;
    LinearAtomManager manager;

    // Helper to assert bounds on an aux var
    auto assertRel = [&](int aux, Relation rel) -> bool {
        switch (rel) {
            case Relation::Eq:
                return gs.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0)))) &&
                       gs.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0))));
            case Relation::Leq:
                return gs.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0))));
            case Relation::Lt:
                return gs.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0, -1))));
            case Relation::Geq:
                return gs.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0))));
            case Relation::Gt:
                return gs.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0, 1))));
            default:
                return true; // Neq not handled here
        }
    };

    // Helper to process a LinearAtomPayload with substitution
    auto processLinearPayload = [&](const LinearAtomPayload& p) -> AssignmentCheckResult {
        LinearFormKey newLhs;
        // Linear RHS is rational (algebraic never arises from inputs).
        mpq_class newRhs = p.rhs.asRational();
        for (const auto& [name, coeff] : p.lhs.terms) {
            auto it = fixedValues.find(name);
            if (it != fixedValues.end()) {
                newRhs -= it->second * coeff;
            } else {
                newLhs.terms.push_back({name, coeff});
            }
        }

        if (newLhs.terms.empty()) {
            bool sat = false;
            switch (p.rel) {
                case Relation::Eq:  sat = (newRhs == 0); break;
                case Relation::Neq: sat = (newRhs != 0); break;
                case Relation::Lt:  sat = (newRhs > 0); break;   // 0 < newRhs
                case Relation::Leq: sat = (newRhs >= 0); break;  // 0 <= newRhs
                case Relation::Gt:  sat = (newRhs < 0); break;   // 0 > newRhs
                case Relation::Geq: sat = (newRhs <= 0); break;  // 0 >= newRhs
            }
            if (!sat) return AssignmentCheckResult::Unsat;
            return AssignmentCheckResult::Sat;
        }

        std::sort(newLhs.terms.begin(), newLhs.terms.end(),
                  [](auto& a, auto& b) { return a.first < b.first; });

        int aux = manager.getOrCreateAuxVar(gs, newLhs, newRhs);
        if (!assertRel(aux, p.rel)) return AssignmentCheckResult::Unsat;
        return AssignmentCheckResult::Sat;
    };

    // Process linear constraints from NIRA active assignments
    for (const auto& a : activeAssignments) {
        if (!a.value) continue;
        if (!std::holds_alternative<LinearAtomPayload>(a.atom.payload)) continue;

        const auto& p = std::get<LinearAtomPayload>(a.atom.payload);
        auto r = processLinearPayload(p);
        if (r != AssignmentCheckResult::Sat) return r;
    }

    // Process linear constraints from LIRA active context
    if (linearCtx) {
        for (const auto& alc : *linearCtx) {
            auto r = processLinearPayload(alc.payload);
            if (r != AssignmentCheckResult::Sat) return r;
        }
    }

    // First pass: count distinct nonlinear polynomial constraints (those that
    // remain non-linear after integer substitution).  If there is more than one
    // *distinct* polynomial, checkUnivariatePoly's per-constraint Sat is unsound
    // — we must fall back to Unknown because we cannot verify their conjunction.
    // Use the *original* poly id for deduplication — two active assignments
    // with the same original polynomial, relation and rhs are the same atom
    // registered twice (e.g. by different theory solvers).
    std::set<std::tuple<PolyId, Relation, RealValue>> distinctNonlinearPolys;
    for (const auto& a : activeAssignments) {
        if (!a.value) continue;
        if (!std::holds_alternative<PolynomialAtomPayload>(a.atom.payload)) continue;

        const auto& p = std::get<PolynomialAtomPayload>(a.atom.payload);
        PolyId current = p.poly;
        for (const auto& [name, value] : fixedValues) {
            auto varIdOpt = kernel->findVar(name);
            if (!varIdOpt) continue;
            auto substituted = kernel->substituteRational(current, *varIdOpt, value);
            if (substituted) current = *substituted;
        }
        if (kernel->isConstant(current)) continue;
        if (!polyToLinearForm(kernel, current)) {
            distinctNonlinearPolys.insert({p.poly, p.rel, p.rhs});
        }
    }
    int nonlinearPolyCount = static_cast<int>(distinctNonlinearPolys.size());

    // Process polynomial constraints (substitute fixed integer values)
    for (const auto& a : activeAssignments) {
        if (!a.value) continue;
        if (!std::holds_alternative<PolynomialAtomPayload>(a.atom.payload)) continue;

        const auto& p = std::get<PolynomialAtomPayload>(a.atom.payload);
        PolyId current = p.poly;

        for (const auto& [name, value] : fixedValues) {
            auto varIdOpt = kernel->findVar(name);
            if (!varIdOpt) continue;
            auto substituted = kernel->substituteRational(current, *varIdOpt, value);
            if (substituted) current = *substituted;
        }

        if (kernel->isConstant(current)) {
            mpq_class val = kernel->toConstant(current);
            bool sat = false;
            switch (p.rel) {
                case Relation::Eq:  sat = (val == 0); break;
                case Relation::Neq: sat = (val != 0); break;
                case Relation::Lt:  sat = (val < 0); break;
                case Relation::Leq: sat = (val <= 0); break;
                case Relation::Gt:  sat = (val > 0); break;
                case Relation::Geq: sat = (val >= 0); break;
            }
            if (!sat) return AssignmentCheckResult::Unsat;
            continue;
        }

        auto linearOpt = polyToLinearForm(kernel, current);
        if (!linearOpt) {
            // Try univariate quadratic / odd-degree analysis before giving up.
            auto uvRes = checkUnivariatePoly(kernel, current, p.rel);
            if (uvRes != UvCheckResult::Unknown) {
                if (uvRes == UvCheckResult::Unsat) return AssignmentCheckResult::Unsat;
                // Soundness fix: per-constraint Sat is only trustworthy when there
                // is exactly one *distinct* nonlinear polynomial.  With multiple
                // different polynomials each may be individually satisfiable while
                // their conjunction is not (e.g. x^2=2 ∧ x^2=3).
                if (nonlinearPolyCount > 1) {
                    return AssignmentCheckResult::Unknown;
                }
                continue;
            }
            // Polynomial still contains real variables after integer substitution.
            // Without full NRA delegation we cannot decide feasibility.
            return AssignmentCheckResult::Unknown;
        }

        auto [lhs, rhs] = *linearOpt;
        int aux = manager.getOrCreateAuxVar(gs, lhs, rhs);
        if (!assertRel(aux, p.rel)) return AssignmentCheckResult::Unsat;
    }

    auto r = gs.check();
    if (r == GeneralSimplex::Result::Sat) return AssignmentCheckResult::Sat;
    if (r == GeneralSimplex::Result::Unsat) return AssignmentCheckResult::Unsat;
    return AssignmentCheckResult::Unknown;
}

TheoryCheckResult NiraSolver::checkBoundedComplete(TheoryLemmaStorage& /*lemmaDb*/) {
    if (!coreIr_ || !kernel_) {
        return TheoryCheckResult::unknown("NIRA: missing CoreIr or PolynomialKernel");
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
        if (!isIntegerVar(coreIr_, name)) continue;

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
            if (!isIntegerVar(coreIr_, name)) continue;

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
            if (isIntegerVar(coreIr_, v)) polyIntVars.insert(v);
        }
    }

    // Step 2c: Also consider integer variables from linear constraints
    // (they may bound real variables even if not appearing in polynomials).
    std::unordered_set<std::string> allIntVars = polyIntVars;
    auto collectIntVarsFromLinear = [&](const LinearAtomPayload& p) {
        for (const auto& [name, coeff] : p.lhs.terms) {
            (void)coeff;
            if (isIntegerVar(coreIr_, name)) allIntVars.insert(name);
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

    if (enumVars.empty()) {
        // No bounded variables to enumerate; cannot make progress.
        return TheoryCheckResult::unknown("NIRA: unbounded integer variable(s)");
    }

    std::sort(enumVars.begin(), enumVars.end());
    std::unordered_map<std::string, mpq_class> fixedValues;
    bool sawUnknown = false;

    std::function<bool(int)> enumerate = [&](int idx) -> bool {
        if (idx == (int)enumVars.size()) {
            auto r = NiraSolver::checkAssignmentWithSimplex(trail(), activeLinearContext_, fixedValues, kernel_.get());
            if (r == AssignmentCheckResult::Sat) return true;
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

    // All enumerated combinations lead to contradiction.
    // Build a conflict clause from the active nonlinear atoms.
    std::vector<SatLit> conflictReasons;
    for (const auto& a : trail()) {
        if (a.value && std::holds_alternative<PolynomialAtomPayload>(a.atom.payload)) {
            conflictReasons.push_back(a.lit);
        }
    }
    if (conflictReasons.empty()) {
        conflictReasons = allActiveReasons();
    }
    return TheoryCheckResult::mkConflict(TheoryConflict{std::move(conflictReasons)});
}

bool NiraSolver::validateOriginalConstraints() const {
    return true;
}

void NiraSolver::onReset() {
    // Base clears the trail; reset the relaxation simplex here.
    gsRelax_.reset();
}

void NiraSolver::setRegistry(TheoryAtomRegistry* reg) {
    registry_ = reg;
}

void NiraSolver::setCoreIr(const CoreIr* ir) {
    coreIr_ = ir;
}

std::optional<TheorySolver::TheoryModel> NiraSolver::getModel() const {
    return std::nullopt;
}

std::vector<SatLit> NiraSolver::allActiveReasons() const {
    std::vector<SatLit> reasons;
    for (const auto& a : trail()) {
        reasons.push_back(a.lit);
    }
    return reasons;
}

} // namespace nlcolver
