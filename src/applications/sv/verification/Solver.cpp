#include "applications/sv/verification/Solver.h"
#include "applications/sv/verification/Transition.h"
#include <somtparser/ir/node.h>
namespace xolver::applications::sv::verification {
Answer Solver::solve(const Problem &problem) {
    Answer answer;
    bool unknown = false;
    if (!decide_) {
        answer.reason = "decision oracle is not attached";
        return answer;
    }
    for (std::size_t i = 0; i < problem.obligations.size(); ++i) {
        const auto &task = problem.obligations[i];
        auto c = task.conclusion;
        if (!c || !c->getSort() || !c->getSort()->isBool()) {
            answer.status = Status::InvalidInput;
            answer.obligation = i;
            answer.reason = "conclusion must be Boolean";
            return answer;
        }
        auto query = task.assumptions;
        for (auto assumption : query)
            if (!assumption || !assumption->getSort() || !assumption->getSort()->isBool()) {
                answer.status = Status::InvalidInput;
                answer.obligation = i;
                answer.reason = "assumptions must be Boolean";
                return answer;
            }
        query.push_back(std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getBool(),
                                                              SOMTParser::NODE_KIND::NT_NOT, "not",
                                                              std::vector<SOMTParser::Node>{c}));
        SolverAnswer result;
        try {
            result = decide_(query);
        } catch (const std::exception &e) {
            answer.obligation = i;
            answer.reason = e.what();
            return answer;
        }
        if (result.result == Result::Sat) {
            answer.status = Status::Invalid;
            answer.obligation = i;
            answer.counterexample = std::move(result.model);
            return answer;
        }
        if (result.result == Result::Unknown && !unknown) {
            unknown = true;
            answer.obligation = i;
            answer.reason = std::move(result.reason);
        }
    }
    answer.status = unknown ? Status::Unknown : Status::Valid;
    return answer;
}
Answer InvariantSolver::solve(const TransitionSystem &system) {
    Answer answer;
    try {
        detail::Transition transition(system, {}, workLimit_);
        transition.statePredicate(system.invariant);
        auto invariantNext = transition.next(system.invariant);
        auto inductiveAssumptions = system.transition;
        inductiveAssumptions.push_back(system.invariant);
        return verification::Solver(decide_).solve(
            {{{"initiation", system.initial, system.invariant},
              {"consecution", inductiveAssumptions, invariantNext},
              {"safety", {system.invariant}, system.safety}}});
    } catch (const std::invalid_argument &e) {
        answer.status = Status::InvalidInput;
        answer.reason = e.what();
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    return answer;
}
} // namespace xolver::applications::sv::verification
