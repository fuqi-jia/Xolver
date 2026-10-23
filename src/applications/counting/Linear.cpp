#include "applications/counting/Linear.h"
#include "algebra/linear/Formula.h"
#include "search/optimization/LinearProgram.h"
#include <functional>
#include <somtparser/ir/node.h>

namespace xolver::applications::counting {
Answer countLinear(const Problem &problem) {
    Answer answer;
    WorkBudget budget(problem.limits.work);
    try {
        NativeTerms terms;
        std::vector<ExprId> assertions, roots;
        for (auto n : problem.assertions)
            assertions.push_back(terms.index(n));
        roots = assertions;
        for (auto n : problem.projection)
            roots.push_back(terms.index(n));
        linear::Formula compiler(terms, roots, budget);
        auto disjunction = compiler.compile(assertions);
        std::vector<std::size_t> projected;
        std::vector<bool> integer;
        for (const auto &v : compiler.variables)
            integer.push_back(v.integer);
        for (auto n : problem.projection) {
            auto it = std::find_if(compiler.variables.begin(), compiler.variables.end(),
                                   [&](const auto &v) { return v.name == n->getName(); });
            if (it == compiler.variables.end() || !it->integer)
                throw linear::UnsupportedFormula(
                    "linear counting requires discrete projected variables");
            projected.push_back(std::size_t(it - compiler.variables.begin()));
        }
        struct Branch {
            optimization::LinearProgram lp;
            std::vector<bool> strict;
        };
        std::vector<Branch> branches;
        std::vector<mpz_class> lower(projected.size()), upper(projected.size());
        bool bounded = false, unknown = false;
        for (const auto &conjunction : disjunction) {
            Branch b;
            b.lp.variables = compiler.variables.size();
            for (const auto &a : conjunction) {
                b.lp.constraints.push_back({a.expression.coefficients, -a.expression.constant});
                b.strict.push_back(a.strict);
            }
            auto witness = optimization::feasible(b.lp, b.strict, integer, budget);
            if (witness.status == optimization::Status::Infeasible)
                continue;
            if (witness.status == optimization::Status::Unknown) {
                unknown = true;
                continue;
            }
            if (projected.empty()) {
                answer.status = Status::Exact;
                answer.count = 1;
                return answer;
            }
            for (std::size_t k = 0; k < projected.size(); ++k) {
                b.lp.objective.assign(b.lp.variables, 0);
                b.lp.objective[projected[k]] = 1;
                b.lp.maximize = false;
                auto lo = optimization::solveMixedInteger(b.lp, integer, budget);
                b.lp.maximize = true;
                auto hi = optimization::solveMixedInteger(b.lp, integer, budget);
                if (lo.status == optimization::Status::Unbounded ||
                    hi.status == optimization::Status::Unbounded) {
                    // A strict feasible integer point plus the rational recession
                    // ray gives infinitely many distinct projected tuples.
                    answer.status = Status::Infinite;
                    return answer;
                }
                if (lo.status != optimization::Status::Optimal ||
                    hi.status != optimization::Status::Optimal)
                    throw ResourceExhausted("counting bound search exhausted");
                const mpz_class l = lo.value->get_num(), h = hi.value->get_num();
                if (!bounded || l < lower[k])
                    lower[k] = l;
                if (!bounded || h > upper[k])
                    upper[k] = h;
            }
            bounded = true;
            branches.push_back(std::move(b));
        }
        if (unknown)
            throw ResourceExhausted("counting feasibility search exhausted");
        if (branches.empty()) {
            answer.status = Status::Exact;
            return answer;
        }
        if (projected.size() > 512)
            throw ResourceExhausted("counting projection depth exhausted");
        std::vector<mpz_class> tuple(projected.size());
        std::function<void(std::size_t)> enumerate = [&](std::size_t k) {
            budget.tick();
            if (k < tuple.size()) {
                for (tuple[k] = lower[k]; tuple[k] <= upper[k]; ++tuple[k])
                    enumerate(k + 1);
                return;
            }
            bool undecided = false;
            for (const auto &branch : branches) {
                auto query = branch.lp;
                auto strict = branch.strict;
                for (std::size_t i = 0; i < tuple.size(); ++i) {
                    optimization::Row row{std::vector<mpq_class>(query.variables),
                                          mpq_class(tuple[i])};
                    row.coefficients[projected[i]] = 1;
                    query.constraints.push_back(row);
                    strict.push_back(false);
                    row.coefficients[projected[i]] = -1;
                    row.rhs = -row.rhs;
                    query.constraints.push_back(std::move(row));
                    strict.push_back(false);
                }
                auto r = optimization::feasible(query, strict, integer, budget);
                if (r.status == optimization::Status::Optimal) {
                    ++answer.count;
                    return;
                }
                undecided |= r.status == optimization::Status::Unknown;
            }
            if (undecided)
                throw ResourceExhausted("projected tuple feasibility budget exhausted");
        };
        enumerate(0);
        answer.status = Status::Exact;
    } catch (const std::invalid_argument &e) {
        answer.status = Status::InvalidInput;
        answer.reason = e.what();
        answer.count = 0;
    } catch (const std::exception &e) {
        answer.status = Status::Unknown;
        answer.reason = e.what();
        answer.count = 0;
    }
    return answer;
}
} // namespace xolver::applications::counting
