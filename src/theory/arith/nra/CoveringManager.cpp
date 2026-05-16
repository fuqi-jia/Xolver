#include "theory/arith/nra/CoveringManager.h"
#include "theory/arith/nra/AlgebraBackend.h"
#include <algorithm>

namespace nlcolver {

// Helper: create a Bound from a RealAlg (preserves exactness for algebraic roots)
static Bound boundFromRealAlg(const RealAlg& ra, bool isOpen) {
    if (ra.isRational()) return Bound::rational(ra.rational, isOpen);
    return Bound::algebraic(ra.root, isOpen);
}

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

// Helper: compare two RealAlgs when algebra backend is unavailable.
// Only handles rational-rational comparison; returns Unknown otherwise.
static CompareResult compareRealAlgFallback(const RealAlg& a, const RealAlg& b) {
    if (a.isRational() && b.isRational()) {
        if (a.rational < b.rational) return CompareResult::Less;
        if (a.rational > b.rational) return CompareResult::Greater;
        return CompareResult::Equal;
    }
    return CompareResult::Unknown;
}

CellLookupResult CoveringManager::cellContaining(
    AlgebraBackend* algebra, VarId var, const RealAlg& sample, const RootSet& roots) {
    // 1. Verify roots is sorted
    for (size_t i = 1; i < roots.roots.size(); ++i) {
        CompareResult c = algebra ? algebra->compareRealAlg(roots.roots[i - 1], roots.roots[i])
                                  : compareRealAlgFallback(roots.roots[i - 1], roots.roots[i]);
        if (c == CompareResult::Unknown) {
            return {CellLookupStatus::Unknown, Cell{}};
        }
        if (c == CompareResult::Equal) {
            return {CellLookupStatus::InvalidInput, Cell{}};
        }
        if (c == CompareResult::Greater) {
            return {CellLookupStatus::InvalidInput, Cell{}};
        }
    }

    // 2. Find sample position among roots
    std::optional<RealAlg> prevRoot;
    for (size_t i = 0; i < roots.roots.size(); ++i) {
        const RealAlg& root = roots.roots[i];
        CompareResult c = algebra ? algebra->compareRealAlg(sample, root)
                                  : compareRealAlgFallback(sample, root);
        if (c == CompareResult::Unknown) {
            return {CellLookupStatus::Unknown, Cell{}};
        }
        if (c == CompareResult::Equal) {
            // Sample equals this root -> Section
            Cell cell;
            cell.var = var;
            cell.kind = CellKind::Section;
            cell.lower = boundFromRealAlg(root, false);
            cell.upper = boundFromRealAlg(root, false);
            return {CellLookupStatus::Found, std::move(cell)};
        }
        if (c == CompareResult::Less) {
            // Sample is before this root -> Sector (prevRoot, root)
            Cell cell;
            cell.var = var;
            cell.kind = CellKind::Sector;
            if (prevRoot) {
                cell.lower = boundFromRealAlg(*prevRoot, true);   // open after prev root
                cell.upper = boundFromRealAlg(root, true);        // open before this root
            } else {
                cell.lower = Bound::negInf();
                cell.upper = boundFromRealAlg(root, true);        // open before this root
            }
            return {CellLookupStatus::Found, std::move(cell)};
        }
        prevRoot = root;
    }

    // 3. Sample is after all roots -> Sector (lastRoot, +inf)
    //    If no roots at all -> FullLine
    Cell cell;
    cell.var = var;
    if (!prevRoot) {
        cell.kind = CellKind::FullLine;
    } else {
        cell.kind = CellKind::Sector;
        cell.lower = boundFromRealAlg(*prevRoot, true);   // open after last root
    }
    if (!prevRoot) {
        cell.lower = Bound::negInf();
    }
    cell.upper = Bound::posInf();
    return {CellLookupStatus::Found, std::move(cell)};
}

} // namespace nlcolver
