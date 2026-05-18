#pragma once

#include "theory/arith/nra/CdcacTypes.h"
#include "theory/TheorySolver.h"
#include <vector>

namespace nlcolver {

// ------------------------------------------------------------------
// V6: SCPR (Set Cover-based Proof Reduction) reason minimization
// ------------------------------------------------------------------
enum class MinimizationLevel : uint8_t {
    L0_Union,       // union + dedup (always sound)
    L1_Greedy,      // greedy set cover (optimization, not required for soundness)
    L2_Exact        // exact/LP reduction (expensive, optional)
};

class ReasonMinimizer {
public:
    // Minimize a set of reasons using the specified level.
    // L0: union + dedup (sound, cheap)
    // L1: greedy deletion (optimization)
    // L2: exact set cover (expensive skeleton)
    static std::vector<SatLit> minimize(
        const Covering& cover,
        const std::vector<SatLit>& reasons,
        MinimizationLevel level = MinimizationLevel::L1_Greedy);

    // L0: simple union + dedup
    static std::vector<SatLit> minimizeL0(const std::vector<SatLit>& reasons);

    // L1: greedy deletion — try removing each reason, keep if still valid
    static std::vector<SatLit> minimizeL1(
        const Covering& cover,
        const std::vector<SatLit>& reasons);

    // L2: exact reduction (skeleton)
    static std::vector<SatLit> minimizeL2(
        const Covering& cover,
        const std::vector<SatLit>& reasons);

    // Validation: every cell's reasons are contained in the kept set
    static bool isValid(const Covering& cover, const std::vector<SatLit>& kept);
};

} // namespace nlcolver
