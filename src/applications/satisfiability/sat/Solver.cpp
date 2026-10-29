#include "applications/satisfiability/sat/Solver.h"
#include <cstdint>
#include <limits>

namespace xolver::applications::satisfiability::sat {

Answer Solver::solve(const Problem& problem) {
    Answer answer;
    auto variable = [](int literal) {
        return static_cast<unsigned>(literal < 0 ? -static_cast<std::int64_t>(literal) : literal);
    };
    auto valid = [&](const Clause& clause) {
        for (const int literal : clause)
            if (!literal || literal == std::numeric_limits<int>::min() ||
                (problem.variables && variable(literal) > problem.variables)) return false;
        return true;
    };
    if (problem.conflicts < 0 || problem.decisions < 0 || !valid(problem.assumptions)) {
        answer.status = Status::InvalidInput;
        answer.reason = "invalid SAT limits or assumptions";
        return answer;
    }
    for (const auto& clause : problem.clauses) {
        if (valid(clause)) continue;
        answer.status = Status::InvalidInput;
        answer.reason = "invalid SAT clause";
        return answer;
    }
    if (std::chrono::steady_clock::now() >= problem.deadline) {
        answer.reason = "SAT deadline expired";
        return answer;
    }
    if (!factory_) { answer.reason = "SAT backend factory is not attached"; return answer; }
    auto backend = factory_();
    if (!backend) { answer.reason = "SAT backend factory returned null"; return answer; }
    backend->setDeadline(problem.deadline);
    if ((problem.conflicts && !backend->limit("conflicts", problem.conflicts)) ||
        (problem.decisions && !backend->limit("decisions", problem.decisions))) {
        answer.reason = "SAT backend does not support the requested budget";
        return answer;
    }
    std::unordered_map<unsigned, SatVar> forward;
    std::unordered_map<SatVar, unsigned> reverse;
    auto literal = [&](int value) {
        const auto index = variable(value);
        auto found = forward.find(index);
        if (found == forward.end()) {
            const auto created = backend->newVar();
            found = forward.emplace(index, created).first;
            reverse.emplace(created, index);
        }
        return SatLit{found->second, value > 0};
    };
    for (const auto& clause : problem.clauses) {
        std::vector<SatLit> encoded;
        for (const int value : clause) encoded.push_back(literal(value));
        backend->addClause(encoded);
    }
    std::vector<SatLit> assumptions;
    for (const int value : problem.assumptions) assumptions.push_back(literal(value));
    const auto result = backend->solve(assumptions);
    if (result == SatSolver::SolveResult::Unsat) {
        answer.status = Status::Unsat;
        for (const auto failed : backend->getFailedAssumptions()) {
            const int index = static_cast<int>(reverse.at(failed.var));
            answer.failedAssumptions.push_back(failed.sign ? index : -index);
        }
    } else if (result == SatSolver::SolveResult::Sat) {
        for (const auto& [index, backendIndex] : forward)
            answer.assignment[index] = backend->value(backendIndex);
        auto satisfied = [&](const Clause& clause) {
            for (const int value : clause)
                if (answer.assignment.at(variable(value)) == (value > 0)) return true;
            return false;
        };
        bool checked = true;
        for (const auto& clause : problem.clauses) checked &= satisfied(clause);
        for (const int value : problem.assumptions) checked &= satisfied(Clause{value});
        if (checked) answer.status = Status::Sat;
        else {
            answer.assignment.clear();
            answer.reason = "SAT backend model failed original-clause validation";
        }
    } else answer.reason = "SAT backend exhausted its budget or returned unknown";
    return answer;
}

} // namespace xolver::applications::satisfiability::sat
