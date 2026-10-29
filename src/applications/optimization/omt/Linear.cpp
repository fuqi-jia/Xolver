#include "applications/optimization/omt/Linear.h"
#include "algebra/linear/Formula.h"
#include "search/optimization/LinearProgram.h"
#include <algorithm>
#include <somtparser/ir/node.h>

namespace xolver::applications::optimization::omt {
namespace {
bool preferable(const Answer &a, const Answer &b, const std::vector<Objective> &objectives) {
    if (b.status == Status::Infeasible)
        return true;
    for (std::size_t i = 0; i < objectives.size(); ++i) {
        const bool au = a.status == Status::Unbounded && i == a.objectiveValues.size();
        const bool bu = b.status == Status::Unbounded && i == b.objectiveValues.size();
        if (au || bu)
            return au && !bu;
        const auto av = *a.objectiveValues.at(i).tryAsRational();
        const auto bv = *b.objectiveValues.at(i).tryAsRational();
        if (av != bv)
            return objectives[i].direction == Direction::Maximize ? av > bv : av < bv;
        const bool ai = a.status == Status::InfimumNotAttained && i + 1 == a.objectiveValues.size();
        const bool bi = b.status == Status::InfimumNotAttained && i + 1 == b.objectiveValues.size();
        if (ai || bi)
            return !ai && bi;
    }
    return false;
}
} // namespace
Answer solveLinear(const Problem &problem) {
    Answer best;
    best.status = Status::Infeasible;
    WorkBudget budget(problem.limits.work);
    try {
        NativeTerms terms;
        std::vector<ExprId> assertions, roots;
        for (auto node : problem.assertions)
            assertions.push_back(terms.index(node));
        roots = assertions;
        for (const auto &o : problem.objectives) {
            if (!o.expression || !o.expression->getSort() || o.order != Order::Arithmetic)
                throw std::invalid_argument(
                    "linear objective requires arithmetic order and a term");
            roots.push_back(terms.index(o.expression));
        }
        linear::Formula compiler(terms, roots, budget);
        auto branches = compiler.compile(assertions);
        std::vector<linear::Affine> objectives;
        for (const auto &o : problem.objectives)
            objectives.push_back(compiler.affine(terms.index(o.expression)));
        std::vector<bool> integers;
        for (const auto &v : compiler.variables)
            integers.push_back(v.integer);
        bool unknown = false;
        for (const auto &branch : branches) {
            optimization::LinearProgram lp;
            lp.variables = compiler.variables.size();
            std::vector<bool> strict;
            for (const auto &a : branch) {
                lp.constraints.push_back({a.expression.coefficients, -a.expression.constant});
                strict.push_back(a.strict);
            }
            auto witness = optimization::feasible(lp, strict, integers, budget);
            if (witness.status == optimization::Status::Infeasible)
                continue;
            if (witness.status == optimization::Status::Unknown) {
                unknown = true;
                continue;
            }
            if (!objectives.empty() &&
                std::find(strict.begin(), strict.end(), true) != strict.end() &&
                std::find(integers.begin(), integers.end(), true) != integers.end()) {
                unknown = true;
                best.reason =
                    "mixed-integer optimization with open real facets requires another backend";
                continue;
            }
            Answer candidate;
            candidate.status = Status::Optimal;
            auto point = witness.point;
            for (std::size_t i = 0; i < objectives.size(); ++i) {
                lp.objective = objectives[i].coefficients;
                lp.offset = objectives[i].constant;
                lp.maximize = problem.objectives[i].direction == Direction::Maximize;
                auto result = optimization::solveMixedInteger(lp, integers, budget);
                if (result.status == optimization::Status::Unknown) {
                    unknown = true;
                    candidate.status = Status::Unknown;
                    break;
                }
                if (result.status == optimization::Status::Unbounded) {
                    candidate.status = Status::Unbounded;
                    break;
                }
                if (result.status != optimization::Status::Optimal)
                    throw std::logic_error("feasible optimization branch became infeasible");
                candidate.objectiveValues.push_back(RealValue::fromMpq(*result.value));
                optimization::Row fixed{lp.objective, *result.value - lp.offset};
                lp.constraints.push_back(fixed);
                strict.push_back(false);
                for (auto &q : fixed.coefficients)
                    q = -q;
                fixed.rhs = -fixed.rhs;
                lp.constraints.push_back(std::move(fixed));
                strict.push_back(false);
                auto attained = optimization::feasible(lp, strict, integers, budget);
                if (attained.status == optimization::Status::Unknown) {
                    unknown = true;
                    candidate.status = Status::Unknown;
                    break;
                }
                if (attained.status == optimization::Status::Infeasible) {
                    candidate.status = Status::InfimumNotAttained;
                    break;
                }
                point = std::move(attained.point);
            }
            if (candidate.status == Status::Unknown)
                continue;
            if (candidate.status == Status::Optimal) {
                candidate.model.emplace();
                for (std::size_t i = 0; i < compiler.variables.size(); ++i) {
                    const auto &v = compiler.variables[i];
                    if (v.boolean)
                        candidate.model->assignments[v.name] = point[i] == 0 ? "false" : "true";
                    else {
                        candidate.model->numericAssignments[v.name] = RealValue::fromMpq(point[i]);
                        candidate.model->assignments[v.name] = point[i].get_str();
                    }
                }
            }
            if (preferable(candidate, best, problem.objectives))
                best = std::move(candidate);
        }
        if (unknown) {
            best.status = Status::Unknown;
            if (best.reason.empty())
                best.reason = "linear optimization search budget exhausted";
        }
    } catch (const std::invalid_argument &e) {
        best = {};
        best.status = Status::InvalidInput;
        best.reason = e.what();
    } catch (const std::exception &e) {
        best.status = Status::Unknown;
        best.reason = e.what();
    }
    return best;
}
} // namespace xolver::applications::optimization::omt
