#include "theory/combination/ConflictMinimizer.h"
#include <algorithm>

namespace xolver {

void ConflictMinimizer::dedup(std::vector<SatLit>& lits) {
    if (lits.size() < 2) return;
    std::sort(lits.begin(), lits.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    lits.erase(std::unique(lits.begin(), lits.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), lits.end());
}

} // namespace xolver
