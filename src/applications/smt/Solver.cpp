#include "applications/smt/Solver.h"
#include "applications/smt/FirstOrderSolver.h"
#include "applications/smt/common/finite/Solver.h"
#include "applications/smt/qffp/Engine.h"
#include "applications/smt/qfs/Engine.h"
#include "ir/NativeFeatures.h"

namespace xolver::applications::smt {
SolverAnswer Solver::solve(const Problem &problem) {
    const auto features = nativeFeatures(problem.assertions);
    SolverAnswer answer;
    if (features.spatial) {
        answer.reason = "spatial operators require an explicit separation-logic request";
        return answer;
    }
    if (features.collections) {
        answer.reason = "sequence/set/bag operators require their native theory backend";
        return answer;
    }
    if (problem.integerEvidence.elimination || problem.integerEvidence.model)
        return solveFirstOrder(problem.assertions, problem.integerLimits, problem.integerEvidence,
                               problem.quantifierLimits);
    if (features.floatingPoint)
        return fp::solve(problem.assertions, problem.quantifierLimits);
    if (features.strings)
        return strings::solve(problem.assertions, problem.quantifierLimits);
    if (features.finiteArray || (features.bitvector && (features.arrays || features.function)) ||
        (features.function && !features.otherSort && !features.real && !features.integerVariable &&
         !features.quantified))
        return finite::solve(problem.assertions, problem.quantifierLimits);
    if (features.quantified || features.bitvector || problem.integerEvidence.elimination ||
        problem.integerEvidence.model)
        return solveFirstOrder(problem.assertions, problem.integerLimits, problem.integerEvidence,
                               problem.quantifierLimits);
    if (ground_)
        return ground_(problem);
    return solveFirstOrder(problem.assertions, problem.integerLimits, problem.integerEvidence,
                           problem.quantifierLimits);
}
} // namespace xolver::applications::smt
