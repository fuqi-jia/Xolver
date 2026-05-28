#pragma once

#include "expr/types.h"

namespace xolver {

enum class LitValue {
    True,
    False,
    Unknown
};

/**
 * Abstract interface for querying SAT assignment state without
 * depending on a specific SAT backend (e.g. CaDiCaL).
 *
 * Implementations must be safe to call from theory check callbacks.
 */
class TheoryAssignmentView {
public:
    virtual ~TheoryAssignmentView() = default;

    /**
     * Return the current value of a literal in the partial/full model.
     * Unknown means the literal has not been assigned yet.
     */
    virtual LitValue value(SatLit lit) const = 0;
};

} // namespace xolver
