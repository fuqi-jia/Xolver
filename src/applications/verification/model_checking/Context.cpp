#include "applications/verification/model_checking/Solver.h"
#include <somtparser/ir/node.h>

namespace xolver::applications::verification::model_checking {
ContextAnswer ContextSolver::solve(const Obligation &task) {
    ContextAnswer answer;
    auto boolean = [](const auto &node) {
        return node && node->getSort() && node->getSort()->isBool();
    };
    if (!boolean(task.conclusion)) {
        answer.implication.status = Status::InvalidInput;
        answer.implication.reason = "conclusion must be Boolean";
        return answer;
    }
    for (const auto &assumption : task.assumptions) {
        if (!boolean(assumption)) {
            answer.implication.status = Status::InvalidInput;
            answer.implication.reason = "assumptions must be Boolean";
            return answer;
        }
    }
    if (!decide_) {
        answer.implication.reason = "decision oracle is not attached";
        return answer;
    }
    try {
        ++answer.queries;
        answer.context = decide_(task.assumptions);
        if (answer.context.result == Result::Unsat) {
            answer.implication.status = Status::Valid;
            return answer;
        }
        auto query = task.assumptions;
        query.push_back(std::make_shared<SOMTParser::DAGNode>(
            SOMTParser::SortManager::getBool(), SOMTParser::NODE_KIND::NT_NOT, "not",
            std::vector<SOMTParser::Node>{task.conclusion}));
        ++answer.queries;
        auto result = decide_(query);
        if (result.result == Result::Unsat) {
            answer.implication.status = Status::Valid;
        } else if (result.result == Result::Sat) {
            answer.implication.status = Status::Invalid;
            answer.implication.counterexample = std::move(result.model);
        } else {
            answer.implication.reason = std::move(result.reason);
        }
    } catch (const std::exception &error) {
        answer.implication.reason = error.what();
    }
    return answer;
}
} // namespace xolver::applications::verification::model_checking
