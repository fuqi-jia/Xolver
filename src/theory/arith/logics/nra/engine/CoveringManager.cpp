#include "theory/arith/logics/nra/engine/CoveringManager.h"
#include "theory/arith/logics/nra/backend/AlgebraBackend.h"
#include <algorithm>

namespace xolver {

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

    // Make a mutable copy for sorting
    std::vector<Cell> cells = cover.cells;

    // Helper to compare two lower/upper bounds
    auto compareBoundValue = [&](const Bound& a, const Bound& b) -> CompareResult {
        if (a.isNegInf() && b.isNegInf()) return CompareResult::Equal;
        if (a.isNegInf()) return CompareResult::Less;
        if (b.isNegInf()) return CompareResult::Greater;
        if (a.isPosInf() && b.isPosInf()) return CompareResult::Equal;
        if (a.isPosInf()) return CompareResult::Greater;
        if (b.isPosInf()) return CompareResult::Less;
        if (!algebra) {
            if (a.value.isRational() && b.value.isRational()) {
                if (a.value.rational < b.value.rational) return CompareResult::Less;
                if (a.value.rational > b.value.rational) return CompareResult::Greater;
                return CompareResult::Equal;
            }
            return CompareResult::Unknown;
        }
        return algebra->compareRealAlg(a.value, b.value);
    };

    // Sort by lower bound value. Must be strict weak ordering.
    std::sort(cells.begin(), cells.end(), [&](const Cell& a, const Cell& b) {
        auto cmp = compareBoundValue(a.lower, b.lower);
        if (cmp == CompareResult::Unknown) {
            return &a < &b;
        }
        if (cmp == CompareResult::Less) return true;
        if (cmp == CompareResult::Greater) return false;
        // Equal lower bounds: tie-breaker for strict weak ordering
        if (a.lower.open != b.lower.open) return !a.lower.open;
        if (a.kind != b.kind) return a.kind == CellKind::Section;
        auto cmpU = compareBoundValue(a.upper, b.upper);
        if (cmpU == CompareResult::Unknown) return &a < &b;
        if (cmpU == CompareResult::Less) return true;
        if (cmpU == CompareResult::Greater) return false;
        return &a < &b;
    });

    // First cell must start at -inf
    if (!cells.front().lower.isNegInf()) {
        return CoverageResult::DoesNotCover;
    }
    // Last cell must end at +inf
    if (!cells.back().upper.isPosInf()) {
        return CoverageResult::DoesNotCover;
    }

    // Check coverage by sweeping left to right.
    // Track the rightmost point that is DEFINITELY covered.
    // For Sector(a,b): covers (a,b). Point b is NOT covered. So covered_to = b (but note b itself is uncovered).
    // For Section{a}: covers {a}. covered_to = a.
    // We need to ensure no gaps between cells.
    for (size_t i = 1; i < cells.size(); ++i) {
        const auto& prev = cells[i - 1];
        const auto& curr = cells[i];

        CompareResult c = boundCompare(algebra, prev.upper, curr.lower);
        if (c == CompareResult::Unknown) {
            return CoverageResult::Unknown;
        }
        if (c == CompareResult::Less) {
            // Definite gap
            return CoverageResult::DoesNotCover;
        }
        if (c == CompareResult::Equal) {
            // Same point. Gap only if BOTH sides are open.
            if (prev.upper.open && curr.lower.open) {
                return CoverageResult::DoesNotCover;
            }
        }
        // c == Greater: overlap, no gap
    }

    return CoverageResult::Covers;
}

PickSampleResult CoveringManager::chooseSampleOutside(
    const Covering& /*cover*/,
    const std::optional<mpq_class>& preferred) {
    // P1: if preferred is given, return it; otherwise return 0.
    if (preferred) {
        return {PickKind::Sample, RealAlg::fromRational(*preferred), CdcacUnknownReason::None};
    }
    return {PickKind::Sample, RealAlg::fromRational(mpq_class(0)), CdcacUnknownReason::None};
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

} // namespace xolver
