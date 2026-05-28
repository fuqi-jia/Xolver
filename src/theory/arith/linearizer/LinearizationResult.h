#pragma once

#include "theory/arith/linearizer/LinearizationTypes.h"
#include "theory/core/TheorySolver.h"
#include <vector>

namespace xolver {

enum class LinearizationStatus {
    NoChange,
    Lemma,
    Unsupported,
    BudgetExceeded
};

struct LinearizationResult {
    LinearizationStatus status;
    std::vector<PendingLinearizationLemma> lemmas;
};

} // namespace xolver
