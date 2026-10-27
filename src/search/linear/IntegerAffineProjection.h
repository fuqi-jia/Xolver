#pragma once

#include "base/WorkBudget.h"
#include "search/linear/IntegerReasoner.h"
#include <map>
#include <unordered_map>

namespace xolver {

// Every integer value of the input form, under the cited equalities, belongs
// to offset + step*Z. A zero step means the form is fixed to offset.
struct IntegerAffineProjection {
    mpz_class offset;
    mpz_class step;
    std::vector<SatLit> reasons;
};

// Immutable snapshot of the current integer equalities. Several projections
// in one theory check share normalization and the variable-to-equation index.
// Build a new context after the active sources change; no simplex state or
// model values are retained here.
class IntegerAffineContext {
public:
    static std::optional<IntegerAffineContext> build(
        const std::vector<ActiveLinearAtom>& activeAtoms, WorkBudget& budget);
    std::optional<IntegerAffineProjection> project(
        const LinearFormKey& form, WorkBudget& budget) const;
    bool empty() const noexcept { return equations_.empty(); }

private:
    struct Equation {
        std::map<std::string, mpz_class> terms;
        mpz_class rhs;
        std::vector<SatLit> reasons;
    };
    std::vector<Equation> equations_;
    std::unordered_map<std::string, std::vector<size_t>> incidence_;
};

// Sparse integral unit-pivot elimination. Unused equalities are safely relaxed;
// unsupported coefficients or exhausted work return no refinement. All state is
// local to this call, including explanations from the current active context.
std::optional<IntegerAffineProjection> projectIntegerAffineForm(
    const LinearFormKey& form, const std::vector<ActiveLinearAtom>& activeAtoms,
    WorkBudget& budget);

} // namespace xolver
