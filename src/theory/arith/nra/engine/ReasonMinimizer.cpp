#include "theory/arith/nra/engine/ReasonMinimizer.h"
#include <algorithm>
#include <unordered_set>

namespace zolver {

// ============================================================================
// Validation
// ============================================================================

static uint32_t litKey(SatLit lit) {
    return (static_cast<uint32_t>(lit.var) << 1) | (lit.sign ? 0u : 1u);
}

bool ReasonMinimizer::isValid(const Covering& cover, const std::vector<SatLit>& kept) {
    std::unordered_set<uint32_t> keptSet;
    keptSet.reserve(kept.size() * 2);
    for (SatLit lit : kept) keptSet.insert(litKey(lit));

    for (const auto& cell : cover.cells) {
        for (SatLit lit : cell.reasons) {
            if (keptSet.find(litKey(lit)) == keptSet.end()) {
                return false;
            }
        }
    }
    return true;
}

// ============================================================================
// L0: Union + dedup
// ============================================================================

std::vector<SatLit> ReasonMinimizer::minimizeL0(const std::vector<SatLit>& reasons) {
    std::vector<SatLit> result = reasons;
    std::sort(result.begin(), result.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    result.erase(std::unique(result.begin(), result.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), result.end());
    return result;
}

// ============================================================================
// L1: Greedy deletion
// ============================================================================

std::vector<SatLit> ReasonMinimizer::minimizeL1(
    const Covering& cover,
    const std::vector<SatLit>& reasons) {

    std::vector<SatLit> result = minimizeL0(reasons);

    // Try removing each reason iteratively
    for (size_t i = 0; i < result.size(); ) {
        auto test = result;
        test.erase(test.begin() + static_cast<std::ptrdiff_t>(i));
        if (isValid(cover, test)) {
            result = std::move(test);
        } else {
            ++i;
        }
    }

    return result;
}

// ============================================================================
// L2: Exact reduction (skeleton)
// ============================================================================

std::vector<SatLit> ReasonMinimizer::minimizeL2(
    const Covering& /*cover*/,
    const std::vector<SatLit>& reasons) {

    // V6 skeleton: exact/LP-based minimization is not yet implemented.
    // Falls back to L1.
    return minimizeL0(reasons);
}

// ============================================================================
// Dispatch
// ============================================================================

std::vector<SatLit> ReasonMinimizer::minimize(
    const Covering& cover,
    const std::vector<SatLit>& reasons,
    MinimizationLevel level) {

    switch (level) {
        case MinimizationLevel::L0_Union:
            return minimizeL0(reasons);
        case MinimizationLevel::L1_Greedy:
            return minimizeL1(cover, reasons);
        case MinimizationLevel::L2_Exact:
            return minimizeL2(cover, reasons);
    }
    return minimizeL0(reasons);
}

} // namespace zolver
