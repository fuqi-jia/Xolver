#include "search/linear/LinearBoundPropagation.h"

#include <algorithm>
#include <array>
#include <deque>
#include <map>
#include <set>
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

struct SharedForm {
    LinearFormKey form;
    std::vector<std::pair<size_t, LinearFormKey>> replacements;
    size_t savings = 0;
};

// A row a*F+b*x rel c can propagate through F without independently choosing
// endpoints for all the other variables. Discover an existing common form;
// never add a solver variable or change simplex/model coordinates.
std::optional<SharedForm> findSharedForm(const std::vector<LinearBoundRow>& rows,
                                        WorkBudget& budget) {
    const auto available = budget.remaining();
    const size_t allowance = available ? *available / 8 : 32768;
    if (!allowance) return std::nullopt;
    WorkBudget discovery(allowance);
    auto tick = [&] { discovery.tick(); budget.tick(); };
    std::optional<SharedForm> best;
    try {
        std::map<std::vector<std::string>, std::vector<size_t>> supports;
        for (size_t index = 0; index < rows.size(); ++index) {
            const auto& terms = rows[index].lhs.terms;
            if (terms.size() < 3) continue; // A replacement must remove terms.
            std::vector<std::string> names;
            for (const auto& [name, coefficient] : terms) {
                (void)coefficient;
                tick();
                names.push_back(name);
            }
            supports[std::move(names)].push_back(index);
        }
        for (const auto& [names, indices] : supports) {
            if (indices.size() < 3) continue;
            std::map<std::vector<mpq_class>, size_t> candidates;
            for (const size_t index : indices) {
                std::vector<mpq_class> coefficients;
                const auto& terms = rows[index].lhs.terms;
                for (const auto& term : terms) {
                    tick();
                    coefficients.emplace_back(term.second / terms.front().second);
                }
                ++candidates[std::move(coefficients)];
            }
            // Frequently asserted forms are the most useful first candidates
            // when the bounded discovery pass cannot inspect every pair.
            std::vector<std::pair<size_t, std::vector<mpq_class>>> ordered;
            for (const auto& [coefficients, frequency] : candidates)
                ordered.emplace_back(frequency, coefficients);
            std::stable_sort(ordered.begin(), ordered.end(),
                [](const auto& a, const auto& b) { return a.first > b.first; });
            for (const auto& [frequency, coefficients] : ordered) {
                (void)frequency;
                SharedForm candidate;
                for (size_t i = 0; i < names.size(); ++i)
                    candidate.form.terms.emplace_back(names[i], coefficients[i]);
                size_t nonproportional = 0;
                for (const size_t index : indices) {
                    const auto& terms = rows[index].lhs.terms;
                    // With at most one exceptional coefficient, one of the
                    // first two ratios is the common multiplier.
                    for (size_t anchor = 0; anchor < 2; ++anchor) {
                        const mpq_class scale = terms[anchor].second / coefficients[anchor];
                        std::optional<size_t> exception;
                        bool matches = true;
                        for (size_t i = 0; i < terms.size(); ++i) {
                            tick();
                            if (terms[i].second == scale * coefficients[i]) continue;
                            if (exception) { matches = false; break; }
                            exception = i;
                        }
                        if (!matches) continue;
                        // Empty name is a placeholder resolved only after a
                        // fresh local form name has been allocated.
                        LinearFormKey replacement{{{"", scale}}};
                        if (exception) {
                            const size_t i = *exception;
                            replacement.terms.emplace_back(names[i],
                                terms[i].second - scale * coefficients[i]);
                            ++nonproportional;
                        }
                        candidate.savings += terms.size() - replacement.terms.size();
                        candidate.replacements.emplace_back(index, std::move(replacement));
                        break;
                    }
                }
                const size_t definitionCost = names.size() + 1;
                if (nonproportional >= 2 && candidate.savings > definitionCost &&
                    (!best || candidate.savings > best->savings)) best = std::move(candidate);
            }
        }
    } catch (const ResourceExhausted&) {
        // Retain only a completely inspected candidate. The remaining budget
        // belongs to ordinary interval propagation, even if discovery stopped.
    }
    return best;
}

} // namespace

std::optional<LinearAggregateConflict> LinearBoundPropagation::aggregateConflict(
    const std::vector<LinearBoundRow>& rows, WorkBudget& budget) {
    try {
        std::array<std::map<std::string, mpq_class>, 2> sums;
        std::array<LinearAggregateConflict, 2> aggregates;
        auto finish = [&](size_t attempt) -> std::optional<LinearAggregateConflict> {
            const auto& sum = sums[attempt];
            auto& aggregate = aggregates[attempt];
            if (!sum.empty() || aggregate.rhs > 0 ||
                (aggregate.rhs == 0 && !aggregate.strict)) return std::nullopt;
            for (const auto& [index, multiplier] : aggregate.multipliers) {
                (void)multiplier;
                budget.tick(rows[index].reasons.size());
                aggregate.reasons.insert(aggregate.reasons.end(), rows[index].reasons.begin(),
                                         rows[index].reasons.end());
            }
            normalizeReasons(aggregate.reasons);
            return aggregate;
        };
        for (size_t index = 0; index < rows.size(); ++index) {
            budget.tick();
            const auto& row = rows[index];
            if (row.rel != Relation::Leq && row.rel != Relation::Lt &&
                row.rel != Relation::Geq && row.rel != Relation::Gt) continue;
            budget.tick(row.reasons.size());
            if (!explained(row.reasons)) continue;
            std::map<std::string, mpq_class> coefficients;
            for (const auto& [variable, coefficient] : row.lhs.terms) {
                budget.tick();
                coefficients[variable] += coefficient;
                if (coefficients[variable] == 0) coefficients.erase(variable);
            }
            const int direction = row.rel == Relation::Geq || row.rel == Relation::Gt ? -1 : 1;
            const bool strict = row.rel == Relation::Lt || row.rel == Relation::Gt;
            if (coefficients.empty()) {
                if (direction * row.rhs < 0 || (row.rhs == 0 && strict))
                    return LinearAggregateConflict{{{index, 1}}, direction * row.rhs, strict, row.reasons};
                continue;
            }
            if (coefficients.size() == 1) continue;
            // A positive scale preserves inequality orientation. Normalize by
            // the first nonzero coefficient's magnitude so equivalent scaled
            // constraints contribute the same form, with exact rational math.
            mpq_class magnitude = coefficients.begin()->second;
            if (magnitude < 0) magnitude = -magnitude;
            for (size_t attempt = 0; attempt < aggregates.size(); ++attempt) {
                const mpq_class multiplier = attempt ? mpq_class(1 / magnitude) : mpq_class(1);
                auto& sum = sums[attempt];
                auto& aggregate = aggregates[attempt];
                for (const auto& [variable, coefficient] : coefficients) {
                    budget.tick();
                    sum[variable] += direction * multiplier * coefficient;
                    if (sum[variable] == 0) sum.erase(variable);
                }
                aggregate.multipliers.emplace_back(index, multiplier);
                aggregate.rhs += direction * multiplier * row.rhs;
                aggregate.strict |= strict;
                // A contradictory prefix is itself a valid nonnegative linear
                // combination; later unrelated rows cannot invalidate its proof.
                if (sum.empty()) {
                    if (auto conflict = finish(attempt)) return conflict;
                }
            }
        }
    } catch (const ResourceExhausted&) {
        // An incomplete aggregate is never a refutation.
    }
    return std::nullopt;
}

std::optional<std::vector<SatLit>> LinearBoundPropagation::findConflict(
    const std::vector<LinearBoundRow>& rows, const IsInteger& isInteger,
    WorkBudget& budget) {
    std::map<std::pair<std::string, bool>, ExplainedLinearBound> bounds;
    std::optional<std::vector<SatLit>> reasons;
    const auto result = run(rows,
        [&](const std::string& variable, bool lower) -> std::optional<ExplainedLinearBound> {
            const auto found = bounds.find({variable, lower});
            return found == bounds.end() ? std::nullopt : std::optional(found->second);
        },
        [&](const std::string& variable, bool lower, const ExplainedLinearBound& bound) {
            const auto key = std::make_pair(variable, lower);
            const auto found = bounds.find(key);
            if (found != bounds.end()) {
                const auto& old = found->second;
                if ((lower ? old.value > bound.value : old.value < bound.value) ||
                    (old.value == bound.value && (old.strict || !bound.strict)))
                    return LinearBoundUpdate::Unchanged;
            }
            bounds[key] = bound;
            const auto opposite = bounds.find({variable, !lower});
            if (opposite != bounds.end() &&
                ((lower ? bound.value > opposite->second.value : bound.value < opposite->second.value) ||
                 (bound.value == opposite->second.value && (bound.strict || opposite->second.strict)))) {
                reasons = bound.reasons;
                reasons->insert(reasons->end(), opposite->second.reasons.begin(), opposite->second.reasons.end());
                normalizeReasons(*reasons);
                return LinearBoundUpdate::Conflict;
            }
            return LinearBoundUpdate::Changed;
        }, isInteger, budget);
    if (!result.conflict) return std::nullopt;
    return result.conflictReasons ? result.conflictReasons : reasons;
}

LinearBoundPropagationResult LinearBoundPropagation::run(
    const std::vector<LinearBoundRow>& input, const Lookup& lookup,
    const Update& update, const IsInteger& isInteger, WorkBudget& budget) {
    LinearBoundPropagationResult result;
    try {
        std::vector<LinearBoundRow> rows;
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
            }
            if (!row.lhs.terms.empty()) rows.push_back(std::move(row));
        }
        std::string sharedName;
        bool sharedInteger = false;
        std::array<std::optional<ExplainedLinearBound>, 2> sharedBounds;
        if (auto shared = findSharedForm(rows, budget)) {
            std::set<std::string> names;
            for (const auto& row : rows)
                for (const auto& [name, coefficient] : row.lhs.terms) {
                    (void)coefficient;
                    budget.tick();
                    names.insert(name);
                }
            sharedName = "__xolver_local_linear_form";
            while (names.contains(sharedName)) sharedName += '_';
            sharedInteger = std::all_of(shared->form.terms.begin(), shared->form.terms.end(),
                [&](const auto& term) { return term.second.get_den() == 1 && isInteger(term.first); });
            for (auto& [index, replacement] : shared->replacements) {
                replacement.terms.front().first = sharedName;
                rows[index].lhs = std::move(replacement);
            }
            LinearBoundRow definition{std::move(shared->form), Relation::Eq, 0, {}};
            definition.lhs.terms.emplace_back(sharedName, -1);
            rows.push_back(std::move(definition));
        }
        auto getBound = [&](const std::string& variable, bool lower) {
            return !sharedName.empty() && variable == sharedName ? sharedBounds[lower]
                                                                 : lookup(variable, lower);
        };
        auto setBound = [&](const std::string& variable, bool lower, const ExplainedLinearBound& bound) {
            if (sharedName.empty() || variable != sharedName) return update(variable, lower, bound);
            auto& old = sharedBounds[lower];
            if (old && ((lower ? old->value > bound.value : old->value < bound.value) ||
                (old->value == bound.value && (old->strict || !bound.strict))))
                return LinearBoundUpdate::Unchanged;
            old = bound;
            const auto& opposite = sharedBounds[!lower];
            if (opposite && (sharedBounds[true]->value > sharedBounds[false]->value ||
                (old->value == opposite->value && (old->strict || opposite->strict)))) {
                result.conflictReasons = old->reasons;
                result.conflictReasons->insert(result.conflictReasons->end(),
                    opposite->reasons.begin(), opposite->reasons.end());
                normalizeReasons(*result.conflictReasons);
                return LinearBoundUpdate::Conflict;
            }
            return LinearBoundUpdate::Changed;
        };
        std::unordered_map<std::string, std::vector<size_t>> incidence;
        for (size_t index = 0; index < rows.size(); ++index)
            for (const auto& [variable, coefficient] : rows[index].lhs.terms) {
                (void)coefficient;
                budget.tick();
                incidence[variable].push_back(index);
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
                    auto endpoint = getBound(variable, direction * coefficient > 0);
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
                // Several endpoints often depend on the same guards. Count
                // their occurrences once; a target excludes only its own
                // contribution, including when a guard also occurs elsewhere.
                using ReasonCounts = std::map<std::pair<SatVar, bool>, size_t>;
                std::optional<ReasonCounts> reasonCounts;
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
                    if ((!sharedName.empty() && variable == sharedName) ? sharedInteger : isInteger(variable)) {
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
                    // The opposite endpoint was used to snapshot the row's
                    // minimum. Consult the desired side separately before
                    // materializing an explanation for an actual improvement.
                    const auto current = getBound(variable, lower);
                    if (current && explained(current->reasons) &&
                        ((lower ? current->value > bound.value : current->value < bound.value) ||
                         (current->value == bound.value && (current->strict || !bound.strict))))
                        continue;
                    if (!reasonCounts) {
                        reasonCounts.emplace();
                        auto count = [&](const std::vector<SatLit>& reasons) {
                            budget.tick(reasons.size());
                            for (SatLit reason : reasons) ++(*reasonCounts)[{reason.var, reason.sign}];
                        };
                        count(row.reasons);
                        for (const auto& endpoint : endpoints) if (endpoint) count(endpoint->reasons);
                    }
                    if (endpoints[target]) {
                        budget.tick(endpoints[target]->reasons.size());
                        for (SatLit reason : endpoints[target]->reasons)
                            --reasonCounts->at({reason.var, reason.sign});
                    }
                    for (const auto& [reason, count] : *reasonCounts) {
                        budget.tick();
                        if (count) bound.reasons.emplace_back(reason.first, reason.second);
                    }
                    if (endpoints[target]) {
                        budget.tick(endpoints[target]->reasons.size());
                        for (SatLit reason : endpoints[target]->reasons)
                            ++reasonCounts->at({reason.var, reason.sign});
                    }
                    const auto changed = setBound(variable, lower, bound);
                    if (changed == LinearBoundUpdate::Conflict) {
                        result.conflict = true;
                        return result;
                    }
                    if (changed != LinearBoundUpdate::Changed) continue;
                    if (variable != sharedName) ++result.updates;
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
