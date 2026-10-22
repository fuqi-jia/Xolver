#pragma once

#include "ir/NativeTerms.h"
#include "applications/Solver.h"
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
enum class OptimizeStatus {
        Optimal,          // attained optimum found
        InfimumNotAttained, // lower bound exists but not reachable
        Unbounded,        // objective can be improved without limit
        Unknown           // solver could not determine
    };

struct OptimizeResult {
        OptimizeStatus status;
        mpq_class objectiveValue; // valid if status == Optimal
        std::vector<ExprId> model; // witness assignment (skeleton)
    };

class Optimize : public applications::TypedSolver<NativeTerms, OptimizeResult> {
public:
    using Status = OptimizeStatus;
    using Result = OptimizeResult;
    applications::Family family() const noexcept override { return applications::Family::Omt; }
    std::string_view name() const noexcept override { return "omt"; }

    // Set the objective function (minimize).
    void setObjective(ExprId objectiveExpr, const NativeTerms& ir);

    // Solve the optimization problem.
    Result solve(const NativeTerms& ir) override;

private:
    ExprId objectiveExpr_ = NullExpr;
    // TODO: objective type detection (linear vs polynomial),
    //       binary search / gradient descent / CAD-based refinement
};

} // namespace xolver
