#include "applications/satisfiability/smt/Solver.h"
#include "search/arith/IntegerBounds.h"
#include "applications/satisfiability/smt/FirstOrderSolver.h"
#include "applications/satisfiability/smt/common/finite/Solver.h"
#include "applications/satisfiability/smt/qffp/Engine.h"
#include "applications/satisfiability/smt/qflira/Engine.h"
#include "applications/satisfiability/smt/qfs/Engine.h"
#include "ir/NativeFeatures.h"

namespace xolver::applications::satisfiability::smt {
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
        (features.function && !features.otherSort && !features.real && !features.integer &&
         !features.quantified))
        return finite::solve(problem.assertions, problem.quantifierLimits);
    if (features.quantified || features.bitvector || problem.integerEvidence.elimination ||
        problem.integerEvidence.model)
        return solveFirstOrder(problem.assertions, problem.integerLimits, problem.integerEvidence,
                               problem.quantifierLimits);
    if (features.nonlinearInteger && !features.real && !features.floatingPoint &&
        !features.strings) {
        // Refute the original conjunction before nonlinear ground search.
        // Linear proof-producing paths keep their existing dispatch.
        auto proof = integer_bounds::refute(problem.assertions, problem.integerLimits.work);
        if (proof.status == integer_bounds::ProofStatus::Proved) {
            answer.result = Result::Unsat;
            return answer;
        }
    }
    if (!features.function && !features.otherSort &&
        ((!ground_ && (features.integer || features.real)) ||
         (features.integerVariable && features.real)))
        if (auto linear = solveLinearArithmetic(problem))
            return *linear;
    if (ground_)
        return ground_(problem);
    return solveFirstOrder(problem.assertions, problem.integerLimits, problem.integerEvidence,
                           problem.quantifierLimits);
}
} // namespace xolver::applications::satisfiability::smt
