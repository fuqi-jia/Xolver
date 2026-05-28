#pragma once

// Backward compatibility alias: SimplexSolver -> LraSolver
#include "theory/arith/lra/LraSolver.h"

namespace xolver {
using SimplexSolver = LraSolver;
} // namespace xolver
