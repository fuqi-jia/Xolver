#include "theory/arith/nra/ReasonManager.h"
#include <algorithm>
#include <unordered_set>

namespace nlcolver {

// V2-8: validation rule for safe redundancy deletion.
// A reason set is valid if every cell's reasons are contained in the kept set.
// This means we can only delete reasons that NO cell references.
static bool validateReasonsStillCover(const Covering& cover,
                                       const std::vector<SatLit>& keptReasons) {
    std::unordered_set<uint32_t> kept;
    kept.reserve(keptReasons.size() * 2);
    for (SatLit lit : keptReasons) {
        kept.insert(lit.var * 2 + (lit.sign ? 1 : 0));
    }

    for (const auto& cell : cover.cells) {
        for (SatLit lit : cell.reasons) {
            uint32_t key = lit.var * 2 + (lit.sign ? 1 : 0);
            if (kept.find(key) == kept.end()) {
                return false;
            }
        }
    }
    return true;
}

std::vector<SatLit> ReasonManager::minimize(const Covering& cover) {
    // Start with the union of all cell reasons, deduplicated
    std::vector<SatLit> allReasons;
    for (const auto& cell : cover.cells) {
        allReasons.insert(allReasons.end(), cell.reasons.begin(), cell.reasons.end());
    }
    allReasons = deduplicate(std::move(allReasons));

    // V2-8a: safe redundancy deletion.
    // Try removing each reason. If validation still passes, keep it removed.
    // Because validation requires every cell's reasons to be in the kept set,
    // this can only delete reasons that no cell references.
    std::vector<SatLit> result;
    result.reserve(allReasons.size());

    for (SatLit lit : allReasons) {
        auto test = result;
        test.push_back(lit);
        // Check if removing 'lit' from allReasons is valid
        // Actually, we test iteratively: try to build result without each reason
        // A simpler approach: test if allReasons without lit is valid
    }

    // Simpler approach: test each reason for removal from the full set
    result = allReasons;
    for (size_t i = 0; i < allReasons.size(); ++i) {
        auto test = result;
        test.erase(std::remove(test.begin(), test.end(), allReasons[i]), test.end());
        if (validateReasonsStillCover(cover, test)) {
            result = std::move(test);
        }
    }

    return result;
}

TheoryConflict ReasonManager::toConflict(const std::vector<SatLit>& reasons) {
    std::vector<SatLit> clause;
    clause.reserve(reasons.size());
    for (SatLit lit : reasons) {
        clause.push_back(lit);
    }
    return TheoryConflict{std::move(clause)};
}

std::vector<SatLit> ReasonManager::deduplicate(std::vector<SatLit> lits) {
    std::sort(lits.begin(), lits.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    lits.erase(std::unique(lits.begin(), lits.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), lits.end());
    return lits;
}

} // namespace nlcolver
