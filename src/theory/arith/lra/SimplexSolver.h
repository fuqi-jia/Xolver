#pragma once

// Backward compatibility alias: SimplexSolver -> LraSolver
#include "theory/arith/lra/LraSolver.h"

namespace nlcolver {
using SimplexSolver = LraSolver;
} // namespace nlcolver
