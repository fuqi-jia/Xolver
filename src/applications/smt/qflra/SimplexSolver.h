#pragma once

// Backward compatibility alias: SimplexSolver -> LraSolver
#include "applications/smt/qflra/LraSolver.h"

namespace xolver {
using SimplexSolver = LraSolver;
} // namespace xolver
