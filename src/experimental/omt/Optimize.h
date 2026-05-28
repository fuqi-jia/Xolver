#pragma once

#include "expr/ir.h"
#include "xolver/Result.h"
#include <string>
#include <vector>
#include <gmpxx.h>

namespace xolver {

/**
 * OMT (Optimization Modulo Theories) Engine.
 *
 * Stage K skeleton:
 *   - Single-objective optimization
 *   - Linear / polynomial objective support
 *   - Attained / InfimumNotAttained / Unbounded classification
 */
class Optimize {
public:
    enum class Status {
        Optimal,          // attained optimum found
        InfimumNotAttained, // lower bound exists but not reachable
        Unbounded,        // objective can be improved without limit
        Unknown           // solver could not determine
    };

    struct Result {
        Status status;
        mpq_class objectiveValue; // valid if status == Optimal
        std::vector<ExprId> model; // witness assignment (skeleton)
    };

    // Set the objective function (minimize).
    void setObjective(ExprId objectiveExpr, const CoreIr& ir);

    // Solve the optimization problem.
    Result solve(const CoreIr& ir);

private:
    ExprId objectiveExpr_ = NullExpr;
    // TODO: objective type detection (linear vs polynomial),
    //       binary search / gradient descent / CAD-based refinement
};

} // namespace xolver
