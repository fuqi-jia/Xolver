#include "applications/optimization/milp/Solver.h"
#include "search/optimization/LinearProgram.h"
#include <set>

namespace xolver::applications::optimization::milp {
Answer Solver::solve(const Problem &problem) {
    Answer answer;
    WorkBudget budget(problem.workLimit);
    try {
        ::xolver::optimization::LinearProgram lp;
        lp.variables = problem.variables.size();
        lp.objective = problem.objective;
        lp.offset = problem.objectiveOffset;
        lp.maximize = problem.maximize;
        std::vector<bool> integer;
        std::set<std::string> names;
        auto bound = [&](std::size_t variable, mpq_class value, bool lower) {
            ::xolver::optimization::Row row{std::vector<mpq_class>(lp.variables), lower ? -value : value};
            row.coefficients[variable] = lower ? -1 : 1;
            lp.constraints.push_back(std::move(row));
        };
        for (std::size_t i = 0; i < lp.variables; ++i) {
            const auto &v = problem.variables[i];
            if (v.name.empty() || !names.insert(v.name).second)
                throw std::invalid_argument("MILP variable names must be unique");
            integer.push_back(v.kind != VariableKind::Continuous);
            if (v.lower)
                bound(i, *v.lower, true);
            if (v.upper)
                bound(i, *v.upper, false);
            if (v.kind == VariableKind::Binary) {
                bound(i, 0, true);
                bound(i, 1, false);
            }
        }
        for (const auto &c : problem.constraints) {
            if (c.relation != Relation::GreaterEqual)
                lp.constraints.push_back({c.coefficients, c.rhs});
            if (c.relation != Relation::LessEqual) {
                auto row = c.coefficients;
                for (auto &q : row)
                    q = -q;
                lp.constraints.push_back({std::move(row), -c.rhs});
            }
        }
        auto result = ::xolver::optimization::solveMixedInteger(lp, integer, budget);
        answer.assignment = std::move(result.point);
        answer.objectiveValue = std::move(result.value);
        switch (result.status) {
        case ::xolver::optimization::Status::Optimal:
            answer.status = Status::Optimal;
            break;
        case ::xolver::optimization::Status::Infeasible:
            answer.status = Status::Infeasible;
            break;
        case ::xolver::optimization::Status::Unbounded:
            answer.status = Status::Unbounded;
            answer.objectiveValue.reset();
            break;
        case ::xolver::optimization::Status::Unknown:
            answer.reason = "mixed-integer search budget exhausted";
            break;
        }
    } catch (const std::invalid_argument &e) {
        answer.status = Status::InvalidInput;
        answer.reason = e.what();
    } catch (const std::bad_alloc &) {
        answer.reason = "MILP memory exhausted";
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    return answer;
}
} // namespace xolver::applications::optimization::milp
