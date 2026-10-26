#pragma once

#include "base/WorkBudget.h"
#include "search/linear/IntegerReasoner.h"

namespace xolver {

// Every integer value of the input form, under the cited equalities, belongs
// to offset + step*Z. A zero step means the form is fixed to offset.
struct IntegerAffineProjection {
    mpz_class offset;
    mpz_class step;
    std::vector<SatLit> reasons;
};

// Sparse integral unit-pivot elimination. Unused equalities are safely relaxed;
// unsupported coefficients or exhausted work return no refinement. All state is
// local to this call, including explanations from the current active context.
std::optional<IntegerAffineProjection> projectIntegerAffineForm(
    const LinearFormKey& form, const std::vector<ActiveLinearAtom>& activeAtoms,
    WorkBudget& budget);

} // namespace xolver
