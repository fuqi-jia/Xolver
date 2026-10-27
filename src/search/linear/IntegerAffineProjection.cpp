#include "search/linear/IntegerAffineProjection.h"

#include <algorithm>
#include <unordered_set>

namespace xolver {

std::optional<IntegerAffineContext> IntegerAffineContext::build(
    const std::vector<ActiveLinearAtom>& activeAtoms, WorkBudget& budget) {
    try {
        IntegerAffineContext context;
        for (const auto& atom : activeAtoms) {
            budget.tick();
            if ((atom.value ? atom.rel : negateRelation(atom.rel)) != Relation::Eq) continue;
            auto normalized = IntegerReasoner::normalize(atom.lhs, atom.rhs, atom.rel, atom.value);
            if (!normalized || normalized->rel != Relation::Eq || normalized->rhs.get_den() != 1) continue;
            Equation row{{}, normalized->rhs.get_num(), {atom.lit}};
            for (const auto& [name, coefficient] : normalized->lhs.terms) {
                budget.tick();
                if (coefficient.get_den() != 1) return std::nullopt;
                row.terms[name] += coefficient.get_num();
                if (row.terms[name] == 0) row.terms.erase(name);
            }
            const size_t index = context.equations_.size();
            for (const auto& [name, coefficient] : row.terms) {
                (void)coefficient;
                context.incidence_[name].push_back(index);
            }
            context.equations_.push_back(std::move(row));
        }
        return context;
    } catch (const ResourceExhausted&) {
        return std::nullopt;
    }
}

std::optional<IntegerAffineProjection> IntegerAffineContext::project(
    const LinearFormKey& form, WorkBudget& budget) const {
    using Coefficients = std::map<std::string, mpz_class>;
    try {
        Coefficients target;
        mpz_class originalStep = 0;
        for (const auto& [name, coefficient] : form.terms) {
            budget.tick();
            if (coefficient.get_den() != 1) return std::nullopt;
            target[name] += coefficient.get_num();
            if (target[name] == 0) target.erase(name);
        }
        for (const auto& [name, coefficient] : target) {
            (void)name;
            budget.tick();
            mpz_gcd(originalStep.get_mpz_t(), originalStep.get_mpz_t(), coefficient.get_mpz_t());
        }
        // Equalities in disjoint variable components cannot affect this form.
        // Keep source ordering inside the relevant component, including every
        // equality connected indirectly through another equation.
        std::vector<size_t> relevant;
        std::vector<bool> visited(equations_.size(), false);
        std::unordered_set<std::string> variables;
        std::vector<std::string> pending;
        for (const auto& [name, coefficient] : target) {
            (void)coefficient;
            variables.insert(name);
            pending.push_back(name);
        }
        while (!pending.empty()) {
            const auto variable = std::move(pending.back());
            pending.pop_back();
            const auto found = incidence_.find(variable);
            if (found == incidence_.end()) continue;
            for (size_t index : found->second) {
                budget.tick();
                if (visited[index]) continue;
                visited[index] = true;
                relevant.push_back(index);
                for (const auto& [name, coefficient] : equations_[index].terms) {
                    (void)coefficient;
                    budget.tick();
                    if (variables.insert(name).second) pending.push_back(name);
                }
            }
        }
        std::sort(relevant.begin(), relevant.end());
        std::vector<Equation> rows;
        rows.reserve(relevant.size());
        for (size_t index : relevant) {
            budget.tick(equations_[index].terms.size() + 1);
            rows.push_back(equations_[index]);
        }
        auto appendReasons = [&](std::vector<SatLit>& to, const std::vector<SatLit>& from) {
            for (const auto literal : from) {
                budget.tick();
                if (std::find(to.begin(), to.end(), literal) == to.end()) to.push_back(literal);
            }
        };
        auto subtract = [&](Coefficients& to, const Coefficients& from, const mpz_class& factor) {
            for (const auto& [name, coefficient] : from) {
                budget.tick();
                to[name] -= factor * coefficient;
                if (to[name] == 0) to.erase(name);
            }
        };
        IntegerAffineProjection result{0, 0, {}};
        while (!rows.empty()) {
            size_t chosen = rows.size();
            std::string variable;
            bool direct = false;
            for (size_t i = 0; i < rows.size(); ++i) {
                for (const auto& [name, coefficient] : rows[i].terms) {
                    budget.tick();
                    if (coefficient != 1 && coefficient != -1) continue;
                    const bool contributes = target.contains(name);
                    if (chosen == rows.size() || (contributes && !direct)) {
                        chosen = i; variable = name; direct = contributes;
                    }
                }
            }
            if (chosen == rows.size()) break;
            Equation pivot = std::move(rows[chosen]);
            rows.erase(rows.begin() + chosen);
            const auto unit = pivot.terms.at(variable);
            if (const auto it = target.find(variable); it != target.end()) {
                const mpz_class factor = it->second / unit;
                subtract(target, pivot.terms, factor);
                result.offset += factor * pivot.rhs;
                appendReasons(result.reasons, pivot.reasons);
            }
            for (auto& row : rows) {
                const auto it = row.terms.find(variable);
                if (it == row.terms.end()) continue;
                const mpz_class factor = it->second / unit;
                subtract(row.terms, pivot.terms, factor);
                row.rhs -= factor * pivot.rhs;
                appendReasons(row.reasons, pivot.reasons);
            }
        }
        for (const auto& [name, coefficient] : target) {
            (void)name;
            budget.tick();
            mpz_gcd(result.step.get_mpz_t(), result.step.get_mpz_t(), coefficient.get_mpz_t());
        }
        // If elimination did not strengthen the lattice, its equality guards
        // are unnecessary. Preserve the original unconditional split instead
        // of weakening its explanation with irrelevant context literals.
        if (result.step == originalStep) return IntegerAffineProjection{0, originalStep, {}};
        std::sort(result.reasons.begin(), result.reasons.end(), [](SatLit a, SatLit b) {
            return a.var != b.var ? a.var < b.var : a.sign < b.sign;
        });
        return result;
    } catch (const ResourceExhausted&) {
        return std::nullopt;
    }
}

std::optional<IntegerAffineProjection> projectIntegerAffineForm(
    const LinearFormKey& form, const std::vector<ActiveLinearAtom>& activeAtoms,
    WorkBudget& budget) {
    auto context = IntegerAffineContext::build(activeAtoms, budget);
    return context ? context->project(form, budget) : std::nullopt;
}

} // namespace xolver
