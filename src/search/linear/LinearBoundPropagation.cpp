#include "search/linear/LinearBoundPropagation.h"

#include <algorithm>
#include <deque>
#include <map>
#include <unordered_map>

namespace xolver {
namespace {

bool explained(const std::vector<SatLit>& reasons) {
    return std::all_of(reasons.begin(), reasons.end(),
        [](SatLit literal) { return literal.var != 0; });
}

void normalizeReasons(std::vector<SatLit>& reasons) {
    std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
        return a.var != b.var ? a.var < b.var : a.sign < b.sign;
    });
    reasons.erase(std::unique(reasons.begin(), reasons.end()), reasons.end());
}

} // namespace

LinearBoundPropagationResult LinearBoundPropagation::run(
    const std::vector<LinearBoundRow>& input, const Lookup& lookup,
    const Update& update, const IsInteger& isInteger, WorkBudget& budget) {
    LinearBoundPropagationResult result;
    try {
        std::vector<LinearBoundRow> rows;
        std::unordered_map<std::string, std::vector<size_t>> incidence;
        for (const auto& source : input) {
            budget.tick();
            if (!explained(source.reasons) || source.rel == Relation::Neq) continue;
            if (source.rel != Relation::Eq && source.rel != Relation::Lt &&
                    source.rel != Relation::Leq && source.rel != Relation::Gt &&
                    source.rel != Relation::Geq) continue;
            // Merge repeated names before selecting a target endpoint.
            std::map<std::string, mpq_class> coefficients;
            for (const auto& [variable, coefficient] : source.lhs.terms) {
                budget.tick();
                coefficients[variable] += coefficient;
            }
            LinearBoundRow row{{}, source.rel, source.rhs, source.reasons};
            for (const auto& [variable, coefficient] : coefficients) {
                if (coefficient == 0) continue;
                row.lhs.terms.emplace_back(variable, coefficient);
                incidence[variable].push_back(rows.size());
            }
            if (!row.lhs.terms.empty()) rows.push_back(std::move(row));
        }
        std::deque<size_t> pending;
        std::vector<bool> queued(rows.size(), true);
        for (size_t i = 0; i < rows.size(); ++i) pending.push_back(i);
        while (!pending.empty()) {
            budget.tick();
            const size_t index = pending.front();
            pending.pop_front();
            queued[index] = false;
            const auto& row = rows[index];
            const int directions = row.rel == Relation::Eq ? 2 : 1;
            for (int pass = 0; pass < directions; ++pass) {
                const int direction = pass || row.rel == Relation::Geq || row.rel == Relation::Gt ? -1 : 1;
                const bool strict = row.rel == Relation::Lt || row.rel == Relation::Gt;
                std::vector<std::optional<ExplainedLinearBound>> endpoints;
                std::vector<mpq_class> contributions;
                size_t missing = 0, strictEndpoints = 0;
                mpq_class minimum = 0;
                // Snapshot the entire row before applying any derived bound.
                for (const auto& [variable, coefficient] : row.lhs.terms) {
                    budget.tick();
                    auto endpoint = lookup(variable, direction * coefficient > 0);
                    if (endpoint && !explained(endpoint->reasons)) endpoint.reset();
                    mpq_class contribution = 0;
                    if (endpoint) {
                        contribution = direction * coefficient * endpoint->value;
                        minimum += contribution;
                        strictEndpoints += endpoint->strict;
                    } else ++missing;
                    endpoints.push_back(std::move(endpoint));
                    contributions.push_back(std::move(contribution));
                }
                for (size_t target = 0; target < endpoints.size(); ++target) {
                    budget.tick();
                    if (missing > size_t(!endpoints[target])) continue;
                    const auto& [variable, coefficient] = row.lhs.terms[target];
                    const mpq_class effectiveCoefficient = direction * coefficient;
                    const bool lower = effectiveCoefficient < 0;
                    ExplainedLinearBound bound;
                    bound.value = (direction * row.rhs - minimum + contributions[target]) /
                                  effectiveCoefficient;
                    bound.strict = strict || strictEndpoints > size_t(endpoints[target] && endpoints[target]->strict);
                    bound.reasons = row.reasons;
                    for (size_t j = 0; j < endpoints.size(); ++j) {
                        if (j == target) continue;
                        budget.tick(endpoints[j]->reasons.size());
                        bound.reasons.insert(bound.reasons.end(), endpoints[j]->reasons.begin(),
                                             endpoints[j]->reasons.end());
                    }
                    if (isInteger(variable)) {
                        mpz_class integer;
                        const auto numerator = bound.value.get_num();
                        const auto denominator = bound.value.get_den();
                        if (lower != bound.strict)
                            mpz_cdiv_q(integer.get_mpz_t(), numerator.get_mpz_t(), denominator.get_mpz_t());
                        else
                            mpz_fdiv_q(integer.get_mpz_t(), numerator.get_mpz_t(), denominator.get_mpz_t());
                        if (bound.strict) integer += lower ? 1 : -1;
                        bound.value = integer;
                        bound.strict = false;
                    }
                    normalizeReasons(bound.reasons);
                    const auto changed = update(variable, lower, bound);
                    if (changed == LinearBoundUpdate::Conflict) {
                        result.conflict = true;
                        return result;
                    }
                    if (changed != LinearBoundUpdate::Changed) continue;
                    ++result.updates;
                    for (const size_t dependent : incidence.at(variable)) {
                        budget.tick();
                        if (!queued[dependent]) {
                            pending.push_back(dependent);
                            queued[dependent] = true;
                        }
                    }
                }
            }
        }
    } catch (const ResourceExhausted&) {
        result.exhausted = true;
    }
    return result;
}

} // namespace xolver
