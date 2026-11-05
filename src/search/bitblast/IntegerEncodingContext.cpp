#include "search/bitblast/IntegerEncodingContext.h"
#include <stdexcept>

namespace xolver::bitblast {
namespace {

SatSolver& requireSolver(const std::unique_ptr<SatSolver>& solver) {
    if (!solver) throw std::invalid_argument("integer encoding requires a SAT solver");
    return *solver;
}

} // namespace

IntegerEncodingContext::IntegerEncodingContext(
    std::unique_ptr<SatSolver> solver, uint64_t variableBudget)
    : solver_(std::move(solver)), encoder_(requireSolver(solver_)) {
    encoder_.setVarBudget(variableBudget);
}

BitVec& IntegerEncodingContext::widen(const std::string& name, unsigned width) {
    if (width == 0) throw std::invalid_argument("integer encoding requires a nonzero width");
    auto& value = variables_[name];
    if (value.width() < width) {
        if (value.isConst) value = encoder_.mkConst(value.constValue, width);
        else {
            const auto extension = encoder_.mkVar(width - value.width());
            value.bits.insert(value.bits.end(), extension.bits.begin(), extension.bits.end());
        }
    }
    return value;
}

} // namespace xolver::bitblast
