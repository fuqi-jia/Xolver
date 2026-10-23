#pragma once
#include "base/WorkBudget.h"
#include <gmpxx.h>
#include <optional>
#include <vector>

namespace xolver::optimization {
// Variables are unrestricted rationals. Every row denotes a*x <= rhs.
struct Row {
    std::vector<mpq_class> coefficients;
    mpq_class rhs = 0;
};
struct LinearProgram {
    std::size_t variables = 0;
    std::vector<Row> constraints;
    std::vector<mpq_class> objective;
    mpq_class offset = 0;
    bool maximize = false;
};
enum class Status { Optimal, Infeasible, Unbounded, Unknown };
struct Solution {
    Status status = Status::Unknown;
    std::optional<mpq_class> value;
    std::vector<mpq_class> point;
    // For Unbounded: a feasible point and a rational improving recession ray.
    std::vector<mpq_class> ray;
};
// Exact two-phase primal simplex with Bland's pivot rule.
Solution solveLinear(const LinearProgram &, WorkBudget &);
// Branch and bound over an arbitrary subset of integer variables. Resource
// exhaustion can retain an incumbent, but never reports it as an optimum.
Solution solveMixedInteger(const LinearProgram &, const std::vector<bool> &integer, WorkBudget &);
// Feasibility with open facets. A common positive slack witnesses every strict
// row; integer variables remain integral while the slack is continuous.
Solution feasible(const LinearProgram &, const std::vector<bool> &strict,
                  const std::vector<bool> &integer, WorkBudget &);
} // namespace xolver::optimization
