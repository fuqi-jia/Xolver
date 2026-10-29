#include "applications/satisfiability/smt/qflira/Engine.h"
#include "algebra/linear/Formula.h"
#include "search/optimization/LinearProgram.h"
namespace xolver::applications::satisfiability::smt {
std::optional<SolverAnswer> solveLinearArithmetic(const Problem &p) {
    SolverAnswer answer;
    WorkBudget budget(p.quantifierLimits.work);
    try {
        NativeTerms terms;
        std::vector<ExprId> roots;
        for (auto n : p.assertions)
            roots.push_back(terms.index(n));
        linear::Formula compiler(terms, roots, budget);
        auto branches = compiler.compile(roots);
        std::vector<bool> integers;
        for (const auto &v : compiler.variables)
            integers.push_back(v.integer);
        bool unknown = false;
        for (const auto &branch : branches) {
            ::xolver::optimization::LinearProgram lp;
            lp.variables = compiler.variables.size();
            std::vector<bool> strict;
            for (const auto &a : branch) {
                lp.constraints.push_back({a.expression.coefficients, -a.expression.constant});
                strict.push_back(a.strict);
            }
            auto result = ::xolver::optimization::feasible(lp, strict, integers, budget);
            if (result.status == ::xolver::optimization::Status::Infeasible)
                continue;
            if (result.status == ::xolver::optimization::Status::Unknown) {
                unknown = true;
                continue;
            }
            answer.result = Result::Sat;
            answer.model.emplace();
            for (std::size_t i = 0; i < compiler.variables.size(); ++i) {
                const auto &v = compiler.variables[i];
                if (v.boolean)
                    answer.model->assignments[v.name] = result.point[i] == 0 ? "false" : "true";
                else {
                    answer.model->numericAssignments[v.name] = RealValue::fromMpq(result.point[i]);
                    answer.model->assignments[v.name] = result.point[i].get_str();
                }
            }
            return answer;
        }
        if (unknown)
            answer.reason = "mixed linear feasibility budget exhausted";
        else
            answer.result = Result::Unsat;
    } catch (const linear::UnsupportedFormula &) {
        return std::nullopt;
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    return answer;
}
} // namespace xolver::applications::satisfiability::smt
