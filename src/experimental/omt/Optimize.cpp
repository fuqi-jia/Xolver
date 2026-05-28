#include "experimental/omt/Optimize.h"

namespace xolver {

void Optimize::setObjective(ExprId objectiveExpr, const CoreIr&) {
    objectiveExpr_ = objectiveExpr;
}

Optimize::Result Optimize::solve(const CoreIr&) {
    // TODO: implement OMT loop (binary search on objective, checkSat calls)
    return Result{Status::Unknown, mpq_class(0), {}};
}

} // namespace xolver
