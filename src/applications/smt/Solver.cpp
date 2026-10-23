#include "applications/smt/Solver.h"
#include "applications/smt/FirstOrderSolver.h"
#include "ir/NativeFeatures.h"

namespace xolver::applications::smt {
SolverAnswer Solver::solve(const Problem& problem) {
    const auto features = nativeFeatures(problem.assertions);
    SolverAnswer answer;
    if (features.spatial) {
        answer.reason = "spatial operators require an explicit separation-logic request";
        return answer;
    }
    if (features.quantified || features.bitvector || problem.integerEvidence.elimination || problem.integerEvidence.model)
        return solveFirstOrder(problem.assertions, problem.integerLimits, problem.integerEvidence, problem.quantifierLimits);
    if (ground_) return ground_(problem);
    answer.reason = "SMT ground session is not attached";
    return answer;
}
} // namespace xolver::applications::smt
