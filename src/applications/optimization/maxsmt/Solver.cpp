#include "applications/optimization/maxsmt/Solver.h"
#include "ir/NativeBuilder.h"
#include <algorithm>
#include <limits>
#include <queue>

namespace xolver::applications::optimization::maxsmt {
namespace {
struct State {
    mpq_class cost = 0;
    std::vector<std::size_t> violated;
};
struct Later {
    bool operator()(const State& a, const State& b) const {
        return a.cost != b.cost ? a.cost > b.cost : a.violated > b.violated;
    }
};
}

Answer Solver::solve(const Problem& problem) {
    Answer answer;
    auto invalid = [&](const std::string& reason) {
        answer.status = Status::InvalidInput;
        answer.reason = reason;
        return answer;
    };
    if (!decide_) {
        answer.reason = "decision oracle is not attached";
        return answer;
    }
    if (problem.limits.stop.stop_requested()) {
        answer.reason = "MaxSMT cancelled";
        return answer;
    }
    NativeAssertions roots = problem.hard;
    auto boolean = [](const auto& node) { return node && node->getSort() && node->getSort()->isBool(); };
    for (const auto& hard : problem.hard)
        if (!boolean(hard)) return invalid("hard constraints must be Boolean formulas");
    std::vector<mpq_class> weights;
    for (const auto& soft : problem.soft) {
        if (!boolean(soft.formula)) return invalid("soft constraints must be Boolean formulas");
        if (soft.weight.get_den() == 0) return invalid("soft weight has a zero denominator");
        mpq_class weight = soft.weight;
        weight.canonicalize();
        if (weight < 0) return invalid("soft weights must be nonnegative");
        weights.push_back(std::move(weight));
        roots.push_back(soft.formula);
    }
    try {
        native::Nodes nodes(roots, problem.limits.formulaWork);
        auto ask = [&](const NativeAssertions& query) {
            nodes.budget.tick();
            if (problem.limits.stop.stop_requested()) throw ResourceExhausted("MaxSMT cancelled");
            if (problem.limits.oracleCalls && answer.oracleCalls >= problem.limits.oracleCalls)
                throw ResourceExhausted("MaxSMT oracle-call limit exhausted");
            if (answer.oracleCalls == std::numeric_limits<std::size_t>::max())
                throw ResourceExhausted("MaxSMT oracle-call counter exhausted");
            ++answer.oracleCalls;
            return decide_(query);
        };
        auto hard = ask(problem.hard);
        if (hard.result == Result::Unsat) {
            answer.status = Status::Infeasible;
            return answer;
        }
        if (problem.soft.empty()) {
            if (hard.result == Result::Sat) {
                answer.status = Status::Optimal;
                answer.cost = 0;
                answer.model = std::move(hard.model);
            } else answer.reason = hard.reason;
            return answer;
        }
        NativeAssertions negated;
        for (const auto& soft : problem.soft) negated.push_back(nodes.negate(soft.formula));
        std::priority_queue<State, std::vector<State>, Later> pending;
        pending.push({});
        answer.generatedStates = 1;
        std::optional<mpq_class> unknownCost;
        while (!pending.empty()) {
            nodes.budget.tick();
            State state = pending.top();
            pending.pop();
            auto query = problem.hard;
            std::size_t next = 0;
            for (std::size_t i = 0; i < problem.soft.size(); ++i) {
                nodes.budget.tick();
                const bool violated = next < state.violated.size() && state.violated[next] == i;
                query.push_back(violated ? negated[i] : problem.soft[i].formula);
                if (violated) ++next;
            }
            auto checked = ask(query);
            if (checked.result == Result::Sat) {
                answer.cost = state.cost;
                answer.violatedSoft = std::move(state.violated);
                answer.model = std::move(checked.model);
                if (!unknownCost || *unknownCost >= state.cost) {
                    answer.status = Status::Optimal;
                    answer.lowerBound = state.cost;
                } else {
                    answer.lowerBound = *unknownCost;
                    answer.reason = "a cheaper soft-constraint assignment remains unknown";
                }
                return answer;
            }
            if (checked.result == Result::Unknown && (!unknownCost || state.cost < *unknownCost))
                unknownCost = state.cost;
            // Increasing indices generate every truth pattern exactly once.
            // Nonnegative weights make the queue's cost order a lower bound.
            const auto first = state.violated.empty() ? 0 : state.violated.back() + 1;
            for (std::size_t i = first; i < problem.soft.size(); ++i) {
                nodes.budget.tick();
                if (problem.limits.states && answer.generatedStates >= problem.limits.states)
                    throw ResourceExhausted("MaxSMT state limit exhausted");
                if (answer.generatedStates == std::numeric_limits<std::size_t>::max())
                    throw ResourceExhausted("MaxSMT state counter exhausted");
                auto child = state;
                child.cost += weights[i];
                child.violated.push_back(i);
                pending.push(std::move(child));
                ++answer.generatedStates;
            }
        }
        if (unknownCost) {
            answer.lowerBound = *unknownCost;
            answer.reason = "soft-constraint assignments remain unknown";
        } else if (hard.result == Result::Sat) {
            answer.reason = "decision oracle returned contradictory satisfiability answers";
        } else answer.status = Status::Infeasible;
    } catch (const std::exception& error) {
        answer.reason = error.what();
    }
    return answer;
}

} // namespace xolver::applications::optimization::maxsmt
