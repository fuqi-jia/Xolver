#pragma once
#include "contracts/PresburgerFormula.h"
#include "xolver/Result.h"
#include <string>

namespace xolver::pa {
// Stable exact JSON. Every QE equation needs independent kernel replay; the
// serialized artifact alone certifies neither the result nor input lowering.
std::string serializeTrace(const EliminationTrace&, Result);
}
