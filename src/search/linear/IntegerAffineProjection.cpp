#include "search/linear/IntegerAffineProjection.h"

#include <algorithm>
#include <map>

namespace xolver {

std::optional<IntegerAffineProjection> projectIntegerAffineForm(
    const LinearFormKey& form, const std::vector<ActiveLinearAtom>& activeAtoms,
    WorkBudget& budget) {
    using Coefficients = std::map<std::string, mpz_class>;
    struct Row {
        Coefficients terms;
        mpz_class rhs;
        std::vector<SatLit> reasons;
    };
    try {
        Coefficients target;
        for (const auto& [name, coefficient] : form.terms) {
            budget.tick();
            if (coefficient.get_den() != 1) return std::nullopt;
            target[name] += coefficient.get_num();
            if (target[name] == 0) target.erase(name);
        }
        std::vector<Row> rows;
        for (const auto& atom : activeAtoms) {
            budget.tick();
            auto normalized = IntegerReasoner::normalize(atom.lhs, atom.rhs, atom.rel, atom.value);
            if (!normalized || normalized->rel != Relation::Eq || normalized->rhs.get_den() != 1) continue;
            Row row{{}, normalized->rhs.get_num(), {atom.lit}};
            for (const auto& [name, coefficient] : normalized->lhs.terms) {
                budget.tick();
                if (coefficient.get_den() != 1) return std::nullopt;
                row.terms[name] += coefficient.get_num();
                if (row.terms[name] == 0) row.terms.erase(name);
            }
            rows.push_back(std::move(row));
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
            Row pivot = std::move(rows[chosen]);
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
        std::sort(result.reasons.begin(), result.reasons.end(), [](SatLit a, SatLit b) {
            return a.var != b.var ? a.var < b.var : a.sign < b.sign;
        });
        return result;
    } catch (const ResourceExhausted&) {
        return std::nullopt;
    }
}

} // namespace xolver
