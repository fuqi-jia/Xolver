#include "search/presolve/PresolveProjection.h"
#include <algorithm>

namespace xolver {

bool reconstructPolynomialDefinitions(const PolynomialDefinitions& definitions,
    std::unordered_map<VarId, mpq_class>& assignment, WorkBudget& work) {
    auto completed = assignment;
    std::set<VarId> pending;
    for (const auto& [variable, polynomial] : definitions) {
        (void)polynomial;
        pending.insert(variable);
    }
    while (!pending.empty()) {
        bool progress = false;
        for (auto it = pending.begin(); it != pending.end();) {
            work.tick();
            const auto variable = *it;
            const auto& polynomial = definitions.at(variable);
            const auto dependencies = polynomial.variables();
            if (std::any_of(dependencies.begin(), dependencies.end(),
                    [&](VarId dependency) {
                        return pending.contains(dependency) || !completed.contains(dependency);
                    })) { ++it; continue; }
            work.tick(polynomial.terms().size());
            const auto value = polynomial.evaluateRational(completed);
            const auto previous = completed.find(variable);
            if (previous != completed.end() && previous->second != value) return false;
            completed[variable] = value;
            it = pending.erase(it);
            progress = true;
        }
        if (!progress) return false;
    }
    assignment = std::move(completed);
    return true;
}

std::optional<PresolveProjection> PresolveProjection::build(
    const PresolveState& state, WorkBudget& work) {
    if (!state.kernel || state.hasConflict || state.hasLemma || state.substMap.empty())
        return std::nullopt;
    PresolveProjection projection;
    projection.integerDomain_ = state.integerDomain;
    for (const auto& atom : state.atoms) {
        work.tick();
        auto reasons = state.ledger.flattenReasons(atom.reasons);
        projection.premises_.insert(projection.premises_.end(), reasons.begin(), reasons.end());
        if (!atom.live) continue;
        const auto converted = atom.poly.toPrimitiveInteger(*state.kernel);
        if (!converted.ok()) return std::nullopt;
        projection.constraints_.push_back({converted.poly, atom.rel, std::move(reasons)});
        const auto variables = atom.poly.variables();
        projection.variables_.insert(variables.begin(), variables.end());
    }
    for (const auto& [variable, definition] : state.substMap) {
        work.tick();
        projection.definitions_.emplace(variable, definition.value);
        for (const auto dependency : definition.vars)
            if (!state.substMap.contains(dependency)) projection.freeVariables_.insert(dependency);
    }
    for (const auto variable : projection.variables_) {
        if (projection.definitions_.contains(variable)) return std::nullopt;
        projection.freeVariables_.insert(variable);
    }
    auto& reasons = projection.premises_;
    std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
        return a.var != b.var ? a.var < b.var : a.sign < b.sign;
    });
    reasons.erase(std::unique(reasons.begin(), reasons.end()), reasons.end());
    return projection;
}

bool PresolveProjection::reconstruct(std::unordered_map<VarId, mpq_class>& assignment,
                                     WorkBudget& work) const {
    auto completed = assignment;
    for (const auto variable : freeVariables_) {
        work.tick();
        if (completed.contains(variable)) continue;
        // A variable absent from every residual atom is unconstrained. Never
        // exploit evaluateRational's missing-variable-as-zero convention.
        if (variables_.contains(variable)) return false;
        completed.emplace(variable, 0);
    }
    if (!reconstructPolynomialDefinitions(definitions_, completed, work)) return false;
    if (integerDomain_ && std::any_of(completed.begin(), completed.end(),
            [](const auto& value) { return value.second.get_den() != 1; })) return false;
    assignment = std::move(completed);
    return true;
}

} // namespace xolver
