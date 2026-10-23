#include "applications/smt/FirstOrderSolver.h"
#include "applications/smt/lia/Solver.h"
#include "quantifiers/FiniteFormula.h"
#include "quantifiers/real/Solver.h"
#include "ir/NativeFeatures.h"

namespace xolver::applications::smt {
SolverAnswer solveFirstOrder(const quantifiers::Roots& roots, pa::Limits integerLimits,
                            pa::EvidenceRequest evidence, quantifiers::Limits limits) {
    const auto features = nativeFeatures(roots);
    SolverAnswer unsupported;
    if (features.spatial || features.function || features.otherSort) {
        unsupported.reason = "first-order input requires an unavailable theory combination";
        return unsupported;
    }
    if (features.bitvector) {
        if (features.real || features.integerVariable || evidence.elimination || evidence.model) {
            unsupported.reason = "first-order bit-vector/integer/real combination is outside the finite-domain signature";
            return unsupported;
        }
        return quantifiers::bitvector::solve(roots, limits);
    }
    if (features.real) {
        if (features.integerVariable || evidence.elimination || evidence.model) {
            unsupported.reason = "first-order mixed integer/real arithmetic requires a mixed-domain algorithm";
            return unsupported;
        }
        return quantifiers::real::solve(roots, limits);
    }
    if (features.integer || evidence.elimination || evidence.model)
        return lia::solve(roots, integerLimits, evidence);
    return quantifiers::boolean::solve(roots, limits);
}
}
