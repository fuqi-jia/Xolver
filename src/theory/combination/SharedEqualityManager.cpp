#include "theory/combination/SharedEqualityManager.h"
#include "theory/core/DebugTrace.h"
#include <algorithm>

namespace nlcolver {

uint64_t SharedEqualityManager::pairKey(SharedTermId a, SharedTermId b) {
    if (a > b) std::swap(a, b);
    return (static_cast<uint64_t>(a) << 32) | static_cast<uint64_t>(b);
}

void SharedEqualityManager::assertEquality(SharedTermId a, SharedTermId b, SatLit reasonLit) {
    NO_DBG << "[SEM] assertEquality st" << a << " = st" << b
           << " reason=" << debug::fmtLit(reasonLit) << "\n";
    // Ensure nodes exist
    while (a >= uf_.size()) uf_.addNode();
    while (b >= uf_.size()) uf_.addNode();
    uf_.unite(a, b, reasonLit);
}

void SharedEqualityManager::assertDisequality(SharedTermId a, SharedTermId b, SatLit reasonLit) {
    NO_DBG << "[SEM] assertDisequality st" << a << " != st" << b
           << " reason=" << debug::fmtLit(reasonLit) << "\n";
    disequalities_.push_back({a, b, reasonLit});
}

bool SharedEqualityManager::same(SharedTermId a, SharedTermId b) const {
    if (a >= uf_.size() || b >= uf_.size()) return a == b;
    return uf_.same(a, b);
}

bool SharedEqualityManager::diseqKnown(SharedTermId a, SharedTermId b) const {
    for (const auto& d : disequalities_) {
        if ((d.a == a && d.b == b) || (d.a == b && d.b == a)) return true;
    }
    return false;
}

std::optional<TheoryConflict> SharedEqualityManager::checkDisequalityConflict() const {
    NO_DBG << "[SEM] checkDisequalityConflict: disequalities=" << disequalities_.size() << "\n";
    for (const auto& d : disequalities_) {
        bool isSame = same(d.a, d.b);
        NO_DBG << "  st" << d.a << " != st" << d.b
               << " sameClass=" << isSame << "\n";
        if (isSame) {
            auto eqReasons = explainEquality(d.a, d.b);
            std::vector<SatLit> conflictLits;
            conflictLits.reserve(eqReasons.size() + 1);
            for (SatLit r : eqReasons) {
                conflictLits.push_back(r);
            }
            conflictLits.push_back(d.reasonLit);
            NO_DBG << "[SEM] CONFLICT: " << debug::fmtClause(conflictLits) << "\n";
            return TheoryConflict{std::move(conflictLits)};
        }
    }
    return std::nullopt;
}

std::vector<SatLit> SharedEqualityManager::explainEquality(SharedTermId a, SharedTermId b) const {
    if (a == b) return {};
    if (!same(a, b)) return {};
    return uf_.explain(a, b);
}

std::vector<SatLit> SharedEqualityManager::explainDisequality(SharedTermId a, SharedTermId b) const {
    for (const auto& d : disequalities_) {
        if ((d.a == a && d.b == b) || (d.a == b && d.b == a)) {
            return {d.reasonLit};
        }
    }
    return {};
}

SharedEqualitySnapshot SharedEqualityManager::snapshot() const {
    return {uf_.snapshot(), disequalities_.size()};
}

void SharedEqualityManager::rollback(SharedEqualitySnapshot snap) {
    uf_.rollback(snap.ufTrailSize);
    disequalities_.resize(snap.diseqSize);
}

void SharedEqualityManager::clear() {
    uf_ = ExplainableRollbackUnionFind<SatLit>();
    disequalities_.clear();
}

} // namespace nlcolver
