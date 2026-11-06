#include "search/refute/PolynomialBooleanRefutation.h"
#include "search/boolean/Atomizer.h"
#include "search/refute/PolynomialSignClosure.h"
#include "search/refute/PolynomialLinearRefutation.h"
#include "search/refute/PolynomialConeRefutation.h"
#include "search/refute/PolynomialResidueRefutation.h"
#include "algebra/poly/PolynomialConverter.h"
#include "base/WorkBudget.h"
#include "base/SolveClock.h"
#include <algorithm>
#include <unordered_map>
#include <unordered_set>

namespace xolver {
namespace {
Relation complement(Relation relation) {
    switch (relation) {
        case Relation::Eq: return Relation::Neq;
        case Relation::Neq: return Relation::Eq;
        case Relation::Lt: return Relation::Geq;
        case Relation::Leq: return Relation::Gt;
        case Relation::Gt: return Relation::Leq;
        case Relation::Geq: return Relation::Lt;
    }
    return relation;
}
Relation relation(Kind kind) {
    switch (kind) {
        case Kind::Eq: return Relation::Eq;
        case Kind::Distinct: return Relation::Neq;
        case Kind::Lt: return Relation::Lt;
        case Kind::Leq: return Relation::Leq;
        case Kind::Gt: return Relation::Gt;
        case Kind::Geq: return Relation::Geq;
        default: throw std::logic_error("not a polynomial comparison");
    }
}
} // namespace

bool refutePolynomialBoolean(const NativeTerms& terms, const std::vector<ExprId>& roots,
    const BooleanRefutationLimits& limits, PolynomialBooleanStatistics* statistics,
    const PolynomialClauseConsumer& consume) {
    PolynomialBooleanStatistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    if (!limits.assignments || roots.empty()) return false;
    wall::DeadlineScope scope(limits.deadline);
#ifndef XOLVER_HAS_LIBPOLY
    return false;
#else
    try {
        WorkBudget work(100000);
        WorkBudget control(0);
        auto tick = [&] {
            work.tick();
            if (std::chrono::steady_clock::now() >= limits.deadline)
                throw ResourceExhausted("Boolean polynomial refutation allocation exhausted");
        };
        auto tickControl = [&] {
            control.tick();
            if (std::chrono::steady_clock::now() >= limits.deadline)
                throw ResourceExhausted("Boolean polynomial refutation deadline exhausted");
        };
        auto sat = createSatSolver();
        Atomizer atomizer(*sat);
        atomizer.setBoolSortId(terms.boolSortId());
        // Full defining equivalences retain both atom polarities independently
        // of the main solver's PG encoding.
        for (auto root : roots) { tick(); sat->addClause({atomizer.atomize(root, terms)}); }
        auto kernel = createPolynomialKernel();
        PolynomialConverter converter(*kernel, &work, limits.deadline);
        std::unordered_map<SatVar, SignRefuteConstraint> polynomials;
        std::unordered_map<SatVar, ExprId> atomExpressions;
        std::unordered_set<SatVar> integerAtoms;
        std::vector<SatVar> atomOrder;
        try {
            for (const auto& atom : atomizer.atoms()) {
                tick();
                const auto node = terms.get(atom.expr);
                if (!node.isAtom() || node.children.size() != 2) continue;
                const auto rel = relation(node.kind);
                const auto converted = converter.convertConstraint(node.children[0], node.children[1], rel, terms);
                if (converted.status == PolyConstraintStatus::Tautology)
                    sat->addTheoryClause({SatLit::positive(atom.var)});
                else if (converted.status == PolyConstraintStatus::Conflict)
                    sat->addTheoryClause({SatLit::negative(atom.var)});
                else if (converted.isConstraint()) {
                    auto polynomial = RationalPolynomial::fromPolyId(converted.diff, *kernel);
                    if (!polynomial) continue;
                    polynomials.emplace(atom.var, SignRefuteConstraint{std::move(*polynomial), rel, {}});
                    atomExpressions.emplace(atom.var, atom.expr);
                    atomOrder.push_back(atom.var);
                }
            }
        } catch (const ResourceExhausted&) {
            // The complete Boolean skeleton remains an overapproximation when
            // the unfinished arithmetic atoms are left uninterpreted. Retain
            // completed exact facts, without retrying the exhausted expansion
            // or accepting any model from this weaker obligation.
            stats.exhausted = true;
            tickControl();
        }
        stats.convertedAtoms = polynomials.size();
        // Conversion already visits declaration leaves. Classify the variables
        // that survive exact cancellation, without walking the source DAG a
        // second time. Delay classification until all observed sort conflicts
        // are known; uncertain declarations never justify integer reasoning.
        std::unordered_set<VarId> integerVariables;
        for (const auto atom : atomOrder) {
            bool integral = true;
            for (const auto variable : polynomials.at(atom).poly.variables()) {
                tickControl();
                const bool integer = converter.variableSort(variable) == SortKind::Int;
                integral &= integer;
                if (integer) integerVariables.insert(variable);
            }
            if (integral) integerAtoms.insert(atom);
        }
        std::vector<VarId> integerDomain;
        for (const auto variable : integerVariables)
            integerDomain.push_back(variable);
        auto select = [&](const SatSolver& model) {
            std::vector<SatLit> selected;
            selected.reserve(atomOrder.size());
            // Keep both true and false arithmetic atoms. A Boolean support
            // may omit useful disequalities on alternative branches; their
            // actual model values are valid premises for explained learning.
            for (auto variable : atomOrder) {
                tickControl();
                selected.emplace_back(variable, model.value(variable));
            }
            return selected;
        };
        // Derived facts can outnumber the original atoms. Share the existing
        // per-check deadline rather than a quota sized for the source context;
        // the refuter retains its independent construction safety bound.
        PolynomialLinearRefuter linearRefuter(0);
        auto oracle = [&](std::span<const SatLit> selected) -> std::optional<std::vector<SatLit>> {
            tickControl();
            stats.largestContext = std::max(stats.largestContext, selected.size());
            if (selected.empty()) return std::nullopt;
            // The exact linear relaxation accepts larger contexts. Each
            // specialized refuter owns its construction limits; a nonlinear
            // closure limit must not suppress the other supported reasoning.
            std::vector<SignRefuteConstraint> constraints;
            std::vector<SignRefuteConstraint> integers;
            for (auto literal : selected) {
                auto constraint = polynomials.at(literal.var);
                if (!literal.sign) constraint.rel = complement(constraint.rel);
                constraint.reason = literal;
                if (integerAtoms.contains(literal.var)) integers.push_back(constraint);
                constraints.push_back(std::move(constraint));
            }
            ++stats.theoryCalls;
            const auto started = std::chrono::steady_clock::now();
            // Cheap product signs can explain a whole Boolean alternative.
            // Prefer them to a weaker conflict between abstract monomial rows,
            // which can leave additional assignments for the SAT solver.
            auto conflict = refuteBySignDefiniteness(constraints);
            if (!conflict && !integers.empty()) {
                PolynomialResidueLimits residueLimits;
                residueLimits.deadline = wall::deadline();
                PolynomialResidueStatistics residue;
                conflict = refuteByPolynomialResidues(integers, residueLimits, &residue);
                ++stats.residueCalls;
                stats.residueAssignments += residue.assignments;
                stats.residueExhaustions += residue.exhausted;
            }
            auto checkLinear = [&](const std::vector<PolynomialConsequence>& consequences) {
                const auto linearStarted = std::chrono::steady_clock::now();
                PolynomialLinearStatistics linear;
                const auto until = wall::deadline();
                auto proof = consequences.empty()
                    ? linearRefuter.check(constraints, until, &linear)
                    : refuteByPolynomialConsequences(linearRefuter, constraints, consequences, until, &linear);
                ++stats.linearCalls;
                stats.linearConstraints += linear.constraints;
                stats.linearSignFacts += linear.signFacts;
                stats.linearMonomialProducts += linear.monomialProducts;
                stats.linearMonomialChecks += linear.monomialDivisibilityChecks;
                stats.linearDisequalityChecks += linear.disequalityChecks;
                stats.linearExhaustions += linear.exhausted;
                stats.linearMicroseconds += std::chrono::duration_cast<std::chrono::microseconds>(
                    std::chrono::steady_clock::now() - linearStarted).count();
                return proof;
            };
            if (!conflict) conflict = checkLinear({});
            std::vector<PolynomialConsequence> consequences;
            if (!conflict) {
                PolynomialSignStatistics sign;
                conflict = refuteByPolynomialSignClosure(constraints, &sign,
                    {.integerVariables = integerDomain}, &consequences);
                stats.signExhaustions += sign.exhausted;
            }
            if (!conflict) {
                conflict = refuteByPolynomialCone(constraints,
                    wall::deadline(),
                    {.integerVariables = integerDomain});
            }
            if (!conflict && !consequences.empty()) conflict = checkLinear(consequences);
            stats.theoryMicroseconds += std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - started).count();
            return conflict;
        };
        auto publish = [&](std::span<const SatLit> clause) {
            if (!consume) return;
            PolynomialTheoryClause translated;
            translated.reserve(clause.size());
            for (const auto literal : clause)
                translated.emplace_back(atomExpressions.at(literal.var), literal.sign);
            consume(translated);
        };
        stats.boolean = refuteBooleanTheory(*sat, select, oracle, limits, publish);
        stats.exhausted |= stats.boolean.exhausted;
        return stats.boolean.refuted;
    } catch (const ResourceExhausted&) {
        stats.exhausted = true;
        return false;
    }
#endif
}
} // namespace xolver
