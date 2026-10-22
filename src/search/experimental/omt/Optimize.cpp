#include "search/experimental/omt/Optimize.h"

namespace xolver {

void Optimize::setObjective(ExprId objectiveExpr, const NativeTerms&) {
    objectiveExpr_ = objectiveExpr;
}

Optimize::Result Optimize::solve(const NativeTerms&) {
    // TODO: implement OMT loop (binary search on objective, checkSat calls)
    return Result{Status::Unknown, mpq_class(0), {}};
}

} // namespace xolver
