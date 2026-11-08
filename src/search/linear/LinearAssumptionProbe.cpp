#include "search/linear/LinearAssumptionProbe.h"
#include <algorithm>
#include <stdexcept>
#include <utility>

namespace xolver {

struct LinearProbeResult::State {
    GeneralSimplex simplex;
    LinearAtomManager manager;
    State(GeneralSimplex&& source, LinearAtomManager&& symbols)
        : simplex(std::move(source)), manager(std::move(symbols)) {}
};

LinearProbeResult::LinearProbeResult() = default;
LinearProbeResult::~LinearProbeResult() = default;
LinearProbeResult::LinearProbeResult(LinearProbeResult&&) noexcept = default;
LinearProbeResult& LinearProbeResult::operator=(LinearProbeResult&&) noexcept = default;

std::optional<LinearProbeModel> LinearProbeResult::model() const {
    if (status != GeneralSimplex::Result::Sat || !state_) return std::nullopt;
    LinearProbeModel model;
    model.delta = state_->simplex.computeSafeDelta();
    for (int variable = 0; variable < state_->simplex.numVars(); ++variable) {
        auto name = state_->manager.getVarName(variable);
        if (!name.empty()) model.assignments.emplace(std::move(name), state_->simplex.value(variable));
    }
    return model;
}

LinearProbeResult probeLinearAssumptions(
    const GeneralSimplex& source, const LinearAtomManager& manager,
    std::span<const LinearProbeAssumption> assumptions,
    std::chrono::steady_clock::time_point deadline) {
    for (const auto& assumption : assumptions) {
        if (assumption.reason.var <= 0)
            throw std::invalid_argument("linear probe needs a valid assumption literal");
        switch (assumption.relation) {
            case Relation::Eq: case Relation::Neq: case Relation::Lt:
            case Relation::Leq: case Relation::Gt: case Relation::Geq: break;
            default: throw std::invalid_argument("invalid linear probe relation");
        }
    }
    LinearProbeResult result;
    auto unknown = [&] {
        // Refuted alternatives alone do not refute an unfinished disjunction.
        result.conflictReasons.clear();
        return std::move(result);
    };
    auto expired = [&] {
        return deadline != std::chrono::steady_clock::time_point::max() &&
               std::chrono::steady_clock::now() >= deadline;
    };
    if (expired()) return unknown();
    GeneralSimplex worker = source;
    LinearAtomManager symbols = manager;
    struct Disequality { int auxiliary; SatLit reason; };
    std::vector<Disequality> disequalities;
    auto rememberConflict = [&] {
        for (const auto& entry : worker.getConflict()) result.conflictReasons.push_back(entry.reason);
    };
    auto finishUnsat = [&] {
        result.status = GeneralSimplex::Result::Unsat;
        std::sort(result.conflictReasons.begin(), result.conflictReasons.end(),
            [](SatLit a, SatLit b) { return a.var != b.var ? a.var < b.var : a.sign < b.sign; });
        result.conflictReasons.erase(
            std::unique(result.conflictReasons.begin(), result.conflictReasons.end()),
            result.conflictReasons.end());
    };
    auto finishSat = [&] {
        result.status = GeneralSimplex::Result::Sat;
        result.conflictReasons.clear();
        result.state_ = std::make_unique<LinearProbeResult::State>(std::move(worker), std::move(symbols));
    };
    auto check = [&] {
        ++result.simplexChecks;
        return worker.checkUntil(deadline);
    };
    for (const auto& assumption : assumptions) {
        if (expired()) return unknown();
        const int auxiliary = symbols.getOrCreateAuxVar(worker, assumption.lhs, assumption.rhs);
        if (assumption.relation == Relation::Neq) {
            disequalities.push_back({auxiliary, assumption.reason});
        } else if (!symbols.assertBound(worker, auxiliary, assumption.relation,
                                        true, assumption.reason)) {
            rememberConflict();
            finishUnsat();
            return result;
        }
    }
    auto status = check();
    if (status == GeneralSimplex::Result::Unknown) return unknown();
    if (status == GeneralSimplex::Result::Unsat) {
        rememberConflict();
        finishUnsat();
        return result;
    }
    // A single copied tableau serves every strict branch. Scope pop restores
    // its bounds and conflict state while preserving valid pivot identities.
    // An explicit stack avoids recursion on conjunctions of disequalities.
    std::vector<unsigned char> choices(disequalities.size(), 0);
    std::size_t depth = 0;
    while (depth < disequalities.size()) {
        if (expired()) return unknown();
        const auto& disjoint = disequalities[depth];
        worker.push();
        ++result.disequalityBranches;
        const bool asserted = symbols.assertBound(worker, disjoint.auxiliary,
            choices[depth] == 0 ? Relation::Lt : Relation::Gt, true, disjoint.reason);
        status = asserted ? check() : GeneralSimplex::Result::Unsat;
        if (status == GeneralSimplex::Result::Unknown) return unknown();
        if (status == GeneralSimplex::Result::Sat) {
            if (++depth < disequalities.size()) choices[depth] = 0;
            continue;
        }
        rememberConflict();
        worker.pop(GeneralSimplex::AssignmentPolicy::Preserve);
        while (choices[depth] != 0) {
            choices[depth] = 0;
            if (depth == 0) {
                // Every strict alternative has been refuted. Keep the source
                // disequality premises explicit in the combined explanation.
                for (const auto& item : disequalities) result.conflictReasons.push_back(item.reason);
                finishUnsat();
                return result;
            }
            --depth;
            worker.pop(GeneralSimplex::AssignmentPolicy::Preserve);
        }
        choices[depth] = 1;
    }
    finishSat();
    return result;
}

} // namespace xolver
