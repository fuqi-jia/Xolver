#pragma once

// Backward compatibility alias: SimplexSolver -> LraSolver
#include "theory/arith/lra/LraSolver.h"

namespace zolver {
using SimplexSolver = LraSolver;
} // namespace zolver
