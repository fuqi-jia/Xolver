#pragma once
#include "ir/NativeTerms.h"
#include "contracts/TheorySolver.h"

namespace xolver {
// Recover concrete numeric array interpretations from a combination model.
// Adopt a candidate only after evaluating every original assertion to true.
bool completeArrayModel(const NativeTerms&, const std::vector<ExprId>&,
                        TheorySolver::TheoryModel&);
}
