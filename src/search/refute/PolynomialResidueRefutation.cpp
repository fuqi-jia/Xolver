#include "search/refute/PolynomialResidueRefutation.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <cstdint>
#include <map>
#include <numeric>

namespace xolver {
namespace {
struct IntegerTerm { MonomialKey powers; mpz_class coefficient; };
struct IntegerEquation { std::vector<IntegerTerm> terms; SatLit reason; };
struct ResidueTerm {
    std::vector<std::pair<size_t, unsigned>> powers;
    uint64_t coefficient;
};
struct ResidueEquation { std::vector<ResidueTerm> terms; SatLit reason; };
} // namespace

std::optional<std::vector<SatLit>> refuteByPolynomialResidues(
    const std::vector<SignRefuteConstraint>& constraints,
    const PolynomialResidueLimits& limits, PolynomialResidueStatistics* statistics) {
    PolynomialResidueStatistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    try {
        WorkBudget work(limits.work);
        auto tick = [&](size_t amount = 1) {
            work.tick(amount);
            if (std::chrono::steady_clock::now() >= limits.deadline)
                throw ResourceExhausted("polynomial residue allocation exhausted");
        };
        tick();
        if (!limits.assignments || !limits.variables) return std::nullopt;
        std::vector<IntegerEquation> integers;
        for (const auto& constraint : constraints) {
            tick();
            if (constraint.rel != Relation::Eq) continue;
            auto polynomial = constraint.poly;
            polynomial.normalize();
            mpz_class denominator = 1;
            for (const auto& [powers, coefficient] : polynomial.terms()) {
                tick(1 + powers.size() + mpz_sizeinbase(coefficient.get_den_mpz_t(), 2));
                mpz_lcm(denominator.get_mpz_t(), denominator.get_mpz_t(), coefficient.get_den_mpz_t());
                if (mpz_sizeinbase(denominator.get_mpz_t(), 2) > 4096)
                    throw ResourceExhausted("polynomial residue coefficient allocation exhausted");
            }
            IntegerEquation equation{{}, constraint.reason};
            mpz_class content = 0;
            for (const auto& [powers, coefficient] : polynomial.terms()) {
                tick(1 + powers.size() + mpz_sizeinbase(coefficient.get_num_mpz_t(), 2));
                mpz_class value = coefficient.get_num() * (denominator / coefficient.get_den());
                mpz_gcd(content.get_mpz_t(), content.get_mpz_t(), value.get_mpz_t());
                equation.terms.push_back({powers, std::move(value)});
            }
            // Dividing a nonzero constant content preserves p=0 over Z.
            if (content > 1) for (auto& term : equation.terms) term.coefficient /= content;
            if (!equation.terms.empty()) integers.push_back(std::move(equation));
        }
        if (integers.empty()) return std::nullopt;
        for (int candidate : limits.moduli) {
            tick();
            // Small composite moduli are valid too; multiplication fits uint64.
            if (candidate < 2 || candidate > 65535) continue;
            const auto modulus = static_cast<uint64_t>(candidate);
            ++stats.moduli;
            std::map<VarId, size_t> columns;
            std::vector<ResidueEquation> equations;
            for (const auto& integer : integers) {
                ResidueEquation equation{{}, integer.reason};
                bool constant = true;
                uint64_t value = 0;
                for (const auto& term : integer.terms) {
                    tick(1 + term.powers.size());
                    const auto coefficient = mpz_fdiv_ui(term.coefficient.get_mpz_t(), modulus);
                    if (!coefficient) continue;
                    ResidueTerm reduced{{}, coefficient};
                    for (const auto& [variable, exponent] : term.powers) {
                        if (exponent <= 0)
                            throw ResourceExhausted("invalid polynomial residue exponent");
                        auto [it, inserted] = columns.try_emplace(variable, columns.size());
                        (void)inserted;
                        reduced.powers.emplace_back(it->second, static_cast<unsigned>(exponent));
                        constant = false;
                    }
                    if (term.powers.empty()) value = (value + coefficient) % modulus;
                    equation.terms.push_back(std::move(reduced));
                }
                if (constant) {
                    if (value) return std::vector<SatLit>{integer.reason};
                } else equations.push_back(std::move(equation));
            }
            std::vector<size_t> parents(columns.size());
            std::iota(parents.begin(), parents.end(), 0);
            auto root = [&](size_t column) {
                while (column != parents[column]) {
                    parents[column] = parents[parents[column]];
                    column = parents[column];
                }
                return column;
            };
            for (const auto& equation : equations) {
                std::optional<size_t> first;
                for (const auto& term : equation.terms) for (const auto& [column, exponent] : term.powers) {
                    (void)exponent;
                    tick();
                    if (!first) first = column;
                    else parents[root(column)] = root(*first);
                }
            }
            struct Component { std::vector<size_t> columns, equations; };
            std::map<size_t, Component> components;
            for (size_t column = 0; column < parents.size(); ++column)
                components[root(column)].columns.push_back(column);
            for (size_t i = 0; i < equations.size(); ++i) {
                for (const auto& term : equations[i].terms) if (!term.powers.empty()) {
                    components[root(term.powers[0].first)].equations.push_back(i);
                    break;
                }
            }
            size_t remaining = limits.assignments;
            std::vector<uint64_t> point(columns.size(), 0);
            for (const auto& [componentRoot, component] : components) {
                (void)componentRoot;
                tick();
                stats.variables = std::max(stats.variables, component.columns.size());
                if (component.columns.size() > limits.variables) { stats.exhausted = true; continue; }
                size_t count = 1;
                bool oversized = false;
                for (size_t i = 0; i < component.columns.size(); ++i) {
                    if (count > remaining / modulus) { oversized = true; break; }
                    count *= modulus;
                }
                if (oversized) { stats.exhausted = true; continue; }
                ++stats.components;
                bool feasible = false;
                for (size_t assignment = 0; assignment < count; ++assignment) {
                    tick();
                    ++stats.assignments;
                    --remaining;
                    bool satisfied = true;
                    for (auto index : component.equations) {
                        ++stats.evaluations;
                        uint64_t value = 0;
                        for (const auto& term : equations[index].terms) {
                            tick();
                            auto product = term.coefficient;
                            for (const auto& [column, exponent] : term.powers) {
                                auto base = point[column];
                                auto power = exponent;
                                uint64_t factor = 1;
                                while (power) {
                                    tick();
                                    if (power & 1) factor = factor * base % modulus;
                                    base = base * base % modulus;
                                    power >>= 1;
                                }
                                product = product * factor % modulus;
                            }
                            value = (value + product) % modulus;
                        }
                        if (value) { satisfied = false; break; }
                    }
                    if (satisfied) { feasible = true; break; }
                    for (auto column : component.columns) {
                        if (++point[column] < modulus) break;
                        point[column] = 0;
                    }
                }
                if (!feasible) {
                    std::vector<SatLit> reasons;
                    for (auto index : component.equations) {
                        auto reason = equations[index].reason;
                        if (std::find(reasons.begin(), reasons.end(), reason) == reasons.end()) reasons.push_back(reason);
                    }
                    return reasons;
                }
            }
        }
    } catch (const ResourceExhausted&) {
        stats.exhausted = true;
    }
    return std::nullopt;
}
} // namespace xolver
