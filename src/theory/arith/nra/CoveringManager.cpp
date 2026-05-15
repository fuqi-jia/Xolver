#include "theory/arith/nra/CoveringManager.h"
#include "theory/arith/nra/AlgebraBackend.h"
#include <algorithm>

namespace nlcolver {

void CoveringManager::addCell(Covering& cover, Cell cell) {
    cover.cells.push_back(std::move(cell));
}

void CoveringManager::normalizeAndMerge(Covering& /*cover*/) {
    // P0: stub. P5: implement cell merge and subsumption deletion.
}

// Helper: compare two bounds for adjacency.
// Returns the CompareResult of their values, or handles infinity bounds.
static CompareResult boundCompare(AlgebraBackend* algebra, const Bound& a, const Bound& b) {
    if (a.isNegInf() && b.isNegInf()) return CompareResult::Equal;
    if (a.isPosInf() && b.isPosInf()) return CompareResult::Equal;
    if (a.isNegInf() || b.isNegInf()) return CompareResult::Less;   // arbitrary, shouldn't happen
    if (a.isPosInf() || b.isPosInf()) return CompareResult::Greater; // arbitrary, shouldn't happen
    if (!algebra) {
        if (a.isRational() && b.isRational()) {
            if (a.value.rational < b.value.rational) return CompareResult::Less;
            if (a.value.rational > b.value.rational) return CompareResult::Greater;
            return CompareResult::Equal;
        }
        return CompareResult::Unknown;
    }
    return algebra->compareRealAlg(a.value, b.value);
}

CoverageResult CoveringManager::coversAllLine(AlgebraBackend* algebra, const Covering& cover) {
    if (cover.cells.empty()) return CoverageResult::DoesNotCover;

    // First cell must start at -inf
    if (!cover.cells.front().lower.isNegInf()) return CoverageResult::DoesNotCover;
    // Last cell must end at +inf
    if (!cover.cells.back().upper.isPosInf()) return CoverageResult::DoesNotCover;

    // Check contiguousness: adjacent cells must meet at the same point,
    // and at least one side must be closed.
    for (size_t i = 1; i < cover.cells.size(); ++i) {
        const auto& prev = cover.cells[i - 1];
        const auto& curr = cover.cells[i];

        CompareResult c = boundCompare(algebra, prev.upper, curr.lower);
        if (c == CompareResult::Unknown) {
            return CoverageResult::Unknown;
        }
        if (c != CompareResult::Equal) {
            return CoverageResult::DoesNotCover;
        }

        // Same point: check open/closed contract.
        // Both sides open means there is a gap at this point.
        if (prev.upper.open && curr.lower.open) {
            return CoverageResult::DoesNotCover;
        }
    }

    return CoverageResult::Covers;
}

std::optional<RealAlg> CoveringManager::chooseSampleOutside(
    const Covering& /*cover*/,
    const std::optional<mpq_class>& preferred) {
    // P1: if preferred is given, return it; otherwise return 0.
    if (preferred) {
        return RealAlg::fromRational(*preferred);
    }
    return RealAlg::fromRational(mpq_class(0));
}

Cell CoveringManager::cellContaining(VarId /*var*/, const RealAlg& /*sample*/, const RootSet& /*roots*/) {
    // P1: stub. P2b: implement.
    return Cell{};
}

} // namespace nlcolver
