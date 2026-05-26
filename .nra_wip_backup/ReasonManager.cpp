#include "theory/arith/nra/ReasonManager.h"
#include <algorithm>

namespace zolver {

std::vector<SatLit> ReasonManager::minimize(const Covering& cover) {
    std::vector<SatLit> reasons;
    for (const auto& cell : cover.cells) {
        reasons.insert(reasons.end(), cell.reasons.begin(), cell.reasons.end());
    }
    return deduplicate(std::move(reasons));
}

TheoryConflict ReasonManager::toConflict(const std::vector<SatLit>& reasons) {
    std::vector<SatLit> clause;
    clause.reserve(reasons.size());
    for (SatLit lit : reasons) {
        clause.push_back(lit.negated());
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

} // namespace zolver
