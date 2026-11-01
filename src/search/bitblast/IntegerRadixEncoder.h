#pragma once

#include "base/WorkBudget.h"
#include "search/bitblast/BitBlastEncoder.h"
#include "search/linear/IntegerAffineModel.h"
#include <chrono>
#include <unordered_map>

namespace xolver::bitblast {

// Share exact bit representations for unconditional integer radix equations.
// Returned indices identify equations made redundant by the emitted definitions
// and domain-fitting clauses. All supplied equations/bounds must be facts of
// this query. This model-construction utility provides no assumption-core
// explanations; an UNSAT-proof caller must separately retain those premises.
std::vector<size_t> encodeIntegerRadixDefinitions(
    BitBlastEncoder& encoder, const std::vector<IntegerRadixDecomposition>& definitions,
    std::unordered_map<std::string, BitVec>& values, const IntegerBoundsLookup& bounds,
    WorkBudget& budget, std::chrono::steady_clock::time_point deadline);

} // namespace xolver::bitblast
