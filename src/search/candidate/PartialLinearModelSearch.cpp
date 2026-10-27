#include "search/candidate/PartialLinearModelSearch.h"
#include "search/candidate/BoundaryCandidates.h"
#include "search/lra/GeneralSimplex.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <chrono>
#include <map>
#include <set>

namespace xolver {
namespace {
struct Endpoint { mpq_class value; bool strict; };
struct Interval { std::optional<Endpoint> lower, upper; };

bool holds(const mpq_class& value, Relation relation) {
    switch (relation) {
        case Relation::Eq: return value == 0;
        case Relation::Neq: return value != 0;
        case Relation::Lt: return value < 0;
        case Relation::Leq: return value <= 0;
        case Relation::Gt: return value > 0;
        case Relation::Geq: return value >= 0;
    }
    return false;
}

Relation flip(Relation relation) {
    switch (relation) {
        case Relation::Lt: return Relation::Gt;
        case Relation::Leq: return Relation::Geq;
        case Relation::Gt: return Relation::Lt;
        case Relation::Geq: return Relation::Leq;
        default: return relation;
    }
}

void tighten(std::optional<Endpoint>& current, Endpoint next, bool lower) {
    if (!current || (lower ? next.value > current->value : next.value < current->value) ||
        (next.value == current->value && next.strict)) current = std::move(next);
}
} // namespace

std::optional<PartialLinearModelSearch::Model> PartialLinearModelSearch::trySolve(
    const std::vector<Constraint>& constraints, PolynomialKernel& kernel, bool integerDomain) {
    try {
        const auto deadline = std::chrono::steady_clock::now() + std::chrono::milliseconds(20);
        WorkBudget budget(100000);
        auto tick = [&]() {
            budget.tick();
            if ((budget.used() & 63) == 0 && std::chrono::steady_clock::now() >= deadline)
                throw ResourceExhausted("partial linear model allocation exhausted");
        };
        using Terms = std::vector<PolynomialKernel::MonomialTerm>;
        std::vector<Terms> atoms;
        std::vector<std::vector<std::pair<VarId, int>>> monomials;
        std::set<VarId> variables, pinned;
        std::map<VarId, Interval> intervals;
        for (const auto& c : constraints) {
            tick();
            if (c.poly == NullPoly) return std::nullopt;
            auto terms = kernel.terms(c.poly);
            if (!terms) return std::nullopt;
            VarId unary = NullVar;
            mpq_class coefficient = 0, constant = 0;
            bool linearUnary = true;
            for (const auto& term : *terms) {
                tick();
                if (term.coefficient == 0) continue;
                unsigned degree = 0;
                for (const auto& [var, exponent] : term.powers) {
                    tick();
                    if (exponent <= 0) return std::nullopt;
                    variables.insert(var);
                    degree += exponent;
                }
                if (degree > 1) monomials.push_back(term.powers);
                if (term.powers.empty()) constant += term.coefficient;
                else if (term.powers.size() == 1 && term.powers[0].second == 1 &&
                         (unary == NullVar || unary == term.powers[0].first)) {
                    unary = term.powers[0].first;
                    coefficient += term.coefficient;
                } else linearUnary = false;
            }
            if (linearUnary && unary != NullVar && coefficient != 0 && c.rel != Relation::Neq) {
                const auto relation = coefficient < 0 ? flip(c.rel) : c.rel;
                const mpq_class value = -constant / coefficient;
                auto& bounds = intervals[unary];
                if (relation == Relation::Eq || relation == Relation::Gt || relation == Relation::Geq)
                    tighten(bounds.lower, {value, relation == Relation::Gt}, true);
                if (relation == Relation::Eq || relation == Relation::Lt || relation == Relation::Leq)
                    tighten(bounds.upper, {value, relation == Relation::Lt}, false);
            }
            atoms.push_back(std::move(*terms));
        }
        if (monomials.empty()) return std::nullopt;

        // A deterministic greedy cover leaves at most one degree-one variable
        // in every monomial. Its complement can then be completed by simplex.
        for (;;) {
            std::map<VarId, size_t> scores;
            for (const auto& monomial : monomials) {
                tick();
                size_t degree = 0;
                for (const auto& [var, exponent] : monomial)
                    if (!pinned.contains(var)) degree += exponent;
                if (degree <= 1) continue;
                for (const auto& [var, exponent] : monomial)
                    if (!pinned.contains(var)) scores[var] += exponent;
            }
            if (scores.empty()) break;
            auto best = scores.begin();
            for (auto it = scores.begin(); it != scores.end(); ++it)
                if (it->second > best->second) best = it;
            pinned.insert(best->first);
        }
        if (pinned.size() == variables.size()) return std::nullopt;

        // Convert endpoints to the client's domain. Open real endpoints are
        // not candidates; integer endpoints are rounded with their strictness.
        for (auto& [var, bounds] : intervals) {
            (void)var;
            if (!integerDomain) continue;
            if (bounds.lower) {
                mpz_class value;
                const auto& q = bounds.lower->value;
                if (bounds.lower->strict) {
                    mpz_fdiv_q(value.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
                    ++value;
                } else mpz_cdiv_q(value.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
                bounds.lower = Endpoint{mpq_class(value), false};
            }
            if (bounds.upper) {
                mpz_class value;
                const auto& q = bounds.upper->value;
                if (bounds.upper->strict) {
                    mpz_cdiv_q(value.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
                    --value;
                } else mpz_fdiv_q(value.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
                bounds.upper = Endpoint{mpq_class(value), false};
            }
        }
        auto admissible = [&](VarId var, const mpq_class& q) {
            const auto& b = intervals[var];
            return (!integerDomain || q.get_den() == 1) &&
                (!b.lower || q > b.lower->value || (q == b.lower->value && !b.lower->strict)) &&
                (!b.upper || q < b.upper->value || (q == b.upper->value && !b.upper->strict));
        };
        auto candidate = [&](VarId var, unsigned mode) -> std::optional<mpq_class> {
            const auto& b = intervals[var];
            std::optional<mpq_class> lo, hi;
            if (b.lower && !b.lower->strict) lo = b.lower->value;
            if (b.upper && !b.upper->strict) hi = b.upper->value;
            auto ends = boundaryCandidates(lo, hi);
            if (mode < 2 && !ends.empty()) {
                const auto q = ends[std::min<size_t>(mode, ends.size() - 1)];
                if (admissible(var, q)) return q;
            }
            mpq_class q = mode == 3 ? 1 : mode == 4 ? -1 : 0;
            if (b.upper && q >= b.upper->value) q = b.upper->value - (b.upper->strict ? 1 : 0);
            if (b.lower && q <= b.lower->value) q = b.lower->value + (b.lower->strict ? 1 : 0);
            if (!admissible(var, q) && b.lower && b.upper) q = (b.lower->value + b.upper->value) / 2;
            return admissible(var, q) ? std::optional<mpq_class>(q) : std::nullopt;
        };

        for (unsigned mode = 0; mode < 5; ++mode) {
            tick();
            Model point;
            for (auto var : pinned) {
                auto q = candidate(var, mode);
                if (!q) return std::nullopt;
                point.emplace(var, *q);
            }
            GeneralSimplex simplex;
            std::map<VarId, int> columns;
            for (auto var : variables)
                if (!pinned.contains(var)) columns[var] = simplex.addVar(std::string(kernel.varName(var)));
            bool feasible = true;
            for (size_t index = 0; index < atoms.size(); ++index) {
                tick();
                std::map<VarId, mpq_class> coefficients;
                mpq_class constant = 0;
                for (const auto& term : atoms[index]) {
                    tick();
                    mpq_class coefficient(term.coefficient);
                    VarId remaining = NullVar;
                    for (const auto& [var, exponent] : term.powers) {
                        tick();
                        if (auto it = point.find(var); it != point.end()) {
                            mpq_class power = 1, base = it->second;
                            for (unsigned e = exponent; e; e >>= 1) {
                                tick();
                                if (e & 1) power *= base;
                                if (e > 1) base *= base;
                            }
                            coefficient *= power;
                        } else {
                            if (remaining != NullVar || exponent != 1) return std::nullopt;
                            remaining = var;
                        }
                    }
                    if (remaining == NullVar) constant += coefficient;
                    else coefficients[remaining] += coefficient;
                }
                std::vector<std::pair<int, mpq_class>> row;
                for (const auto& [var, coefficient] : coefficients)
                    if (coefficient != 0) row.emplace_back(columns.at(var), coefficient);
                const auto relation = constraints[index].rel;
                if (row.empty()) {
                    if (!holds(constant, relation)) { feasible = false; break; }
                    continue;
                }
                if (relation == Relation::Neq) continue; // validated at the completed point
                const int auxiliary = simplex.addConstraint(row, -constant);
                if (auxiliary < 0) return std::nullopt;
                const auto reason = SatLit::positive(1); // local; never exported
                if (relation == Relation::Eq || relation == Relation::Gt || relation == Relation::Geq)
                    feasible &= simplex.assertLower(auxiliary, BoundInfo(BoundValue(
                        DeltaRational(0, relation == Relation::Gt ? 1 : 0)), reason));
                if (relation == Relation::Eq || relation == Relation::Lt || relation == Relation::Leq)
                    feasible &= simplex.assertUpper(auxiliary, BoundInfo(BoundValue(
                        DeltaRational(0, relation == Relation::Lt ? -1 : 0)), reason));
                if (!feasible) break;
            }
            if (!feasible || simplex.checkUntil(deadline) != GeneralSimplex::Result::Sat) continue;
            const auto delta = simplex.computeSafeDelta();
            for (const auto& [var, column] : columns) {
                const auto value = simplex.value(column);
                point.emplace(var, value.a + value.b * delta);
            }
            bool valid = true;
            if (integerDomain)
                for (const auto& [var, q] : point) { (void)var; valid &= q.get_den() == 1; }
            for (const auto& constraint : constraints) {
                tick();
                const int sign = kernel.sgnVarId(constraint.poly, point);
                if (!holds(mpq_class(sign), constraint.rel)) { valid = false; break; }
            }
            if (valid) return point;
        }
    } catch (const std::exception&) {
        // Unsupported arithmetic and exhaustion leave the caller's search open.
    }
    return std::nullopt;
}
} // namespace xolver
