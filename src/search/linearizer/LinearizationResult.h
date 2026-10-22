#pragma once

#include "search/linearizer/LinearizationTypes.h"
#include "contracts/TheorySolver.h"
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
