#include "applications/optimization/maxsat/Solver.h"
#include "ir/NativeBuilder.h"
#include <cstdint>
#include <limits>
#include <unordered_map>

namespace xolver::applications::optimization::maxsat {

Answer Solver::solve(const Problem& problem) {
    Answer answer;
    if (problem.limits.stop.stop_requested()) {
        answer.reason = "MaxSAT cancelled";
        return answer;
    }
    auto valid = [&](const Clause& clause) {
        for (const int literal : clause) {
            if (!literal || literal == std::numeric_limits<int>::min()) return false;
            const auto variable = static_cast<std::uint64_t>(
                literal < 0 ? -static_cast<std::int64_t>(literal) : literal);
            if (problem.variables && variable > problem.variables) return false;
        }
        return true;
    };
    for (const auto& clause : problem.hard) {
        if (valid(clause)) continue;
        answer.status = Status::InvalidInput;
        answer.reason = "invalid hard-clause variable index";
        return answer;
    }
    for (const auto& clause : problem.soft) {
        if (valid(clause.literals)) continue;
        answer.status = Status::InvalidInput;
        answer.reason = "invalid soft-clause variable index";
        return answer;
    }
    try {
        native::Nodes nodes({}, problem.limits.formulaWork);
        using Node = std::shared_ptr<SOMTParser::DAGNode>;
        std::unordered_map<std::uint32_t, Node> variables;
        auto formula = [&](const Clause& clause) {
            std::vector<Node> literals;
            for (const int literal : clause) {
                nodes.budget.tick();
                const auto index = static_cast<std::uint32_t>(
                    literal < 0 ? -static_cast<std::int64_t>(literal) : literal);
                auto found = variables.find(index);
                if (found == variables.end())
                    found = variables.emplace(index, nodes.make(SOMTParser::SortManager::getBool(),
                        native::K::NT_VAR, {}, "_maxsat_" + std::to_string(index))).first;
                literals.push_back(literal > 0 ? found->second : nodes.negate(found->second));
            }
            return nodes.any(std::move(literals));
        };
        maxsmt::Problem request;
        request.limits = problem.limits;
        for (const auto& clause : problem.hard) request.hard.push_back(formula(clause));
        for (const auto& clause : problem.soft)
            request.soft.push_back({formula(clause.literals), clause.weight, clause.label});
        if (problem.limits.formulaWork) {
            const auto used = nodes.budget.used();
            if (used >= problem.limits.formulaWork)
                throw ResourceExhausted("MaxSAT formula-work limit exhausted");
            request.limits.formulaWork -= used;
        }
        return maxsmt::Solver(decide_).solve(request);
    } catch (const std::exception& error) {
        answer.reason = error.what();
        return answer;
    }
}

} // namespace xolver::applications::optimization::maxsat
