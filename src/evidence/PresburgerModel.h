#pragma once
#include "contracts/PresburgerFormula.h"
#include <optional>

namespace xolver::pa {
struct ModelCheck {
    std::optional<bool> holds;
    uint64_t steps = 0;
    std::string reason;
};
// Checks exact integer inequalities/divisibility and Boolean domains. Zero
// steps means no work is allowed. This checker does not link the PA engine.
ModelCheck checkModel(const ModelEvidence&, uint64_t maxSteps = 1000000);
} // namespace xolver::pa
