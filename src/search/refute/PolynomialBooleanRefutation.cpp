#include "search/refute/PolynomialBooleanRefutation.h"
#include "search/boolean/Atomizer.h"
#include "search/refute/PolynomialSignClosure.h"
#include "search/refute/PolynomialLinearRefutation.h"
#include "algebra/poly/PolynomialConverter.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <unordered_map>

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
    const BooleanRefutationLimits& limits, PolynomialBooleanStatistics* statistics) {
    PolynomialBooleanStatistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    if (!limits.assignments || roots.empty()) return false;
#ifndef XOLVER_HAS_LIBPOLY
    return false;
#else
    try {
        WorkBudget work(100000);
        auto tick = [&] {
            work.tick();
            if (std::chrono::steady_clock::now() >= limits.deadline)
                throw ResourceExhausted("Boolean polynomial refutation allocation exhausted");
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
        std::vector<SatVar> atomOrder;
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
                atomOrder.push_back(atom.var);
            }
        }
        stats.convertedAtoms = polynomials.size();
        auto select = [&](const SatSolver& model) {
            std::vector<SatLit> selected;
            selected.reserve(atomOrder.size());
            // Keep both true and false arithmetic atoms. A Boolean support
            // may omit useful disequalities on alternative branches; their
            // actual model values are valid premises for explained learning.
            for (auto variable : atomOrder) {
                tick();
                selected.emplace_back(variable, model.value(variable));
            }
            return selected;
        };
        auto oracle = [&](std::span<const SatLit> selected) -> std::optional<std::vector<SatLit>> {
            tick();
            stats.largestContext = std::max(stats.largestContext, selected.size());
            if (selected.empty() || selected.size() > 128) return std::nullopt;
            std::vector<SignRefuteConstraint> constraints;
            for (auto literal : selected) {
                auto constraint = polynomials.at(literal.var);
                if (!literal.sign) constraint.rel = complement(constraint.rel);
                constraint.reason = literal;
                constraints.push_back(std::move(constraint));
            }
            ++stats.theoryCalls;
            const auto started = std::chrono::steady_clock::now();
            PolynomialLinearStatistics linear;
            auto conflict = refutePolynomialLinearRelaxation(constraints,
                std::min(limits.deadline, started + std::chrono::milliseconds(2)), &linear);
            ++stats.linearCalls;
            stats.linearConstraints += linear.constraints;
            stats.linearExhaustions += linear.exhausted;
            stats.linearMicroseconds += std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - started).count();
            if (!conflict) conflict = refuteBySignDefiniteness(constraints);
            if (!conflict) {
                PolynomialSignStatistics sign;
                conflict = refuteByPolynomialSignClosure(constraints, &sign);
                stats.signExhaustions += sign.exhausted;
            }
            stats.theoryMicroseconds += std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - started).count();
            return conflict;
        };
        stats.boolean = refuteBooleanTheory(*sat, select, oracle, limits);
        stats.exhausted = stats.boolean.exhausted;
        return stats.boolean.refuted;
    } catch (const ResourceExhausted&) {
        stats.exhausted = true;
        return false;
    }
#endif
}
} // namespace xolver
