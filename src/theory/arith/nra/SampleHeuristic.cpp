#include "theory/arith/nra/SampleHeuristic.h"
#include "theory/arith/nra/AlgebraBackend.h"

namespace nlcolver {

SampleHeuristic::SampleHeuristic(AlgebraBackend* algebra)
    : algebra_(algebra) {}

SampleHeuristicResult SampleHeuristic::pick(
    VarId var,
    const Cell& cell,
    const std::optional<mpq_class>& seed,
    SampleStrategy strategy) {

    (void)var;
    (void)strategy;

    switch (cell.kind) {
        case CellKind::Sector:
            return pickSector(var, cell.lower, cell.upper, seed);
        case CellKind::Section:
            if (cell.lower.isRational()) {
                return pickSection(var, RealAlg::fromRational(cell.lower.value.rational));
            }
            if (cell.lower.isAlgebraic()) {
                return pickSection(var, RealAlg::fromAlgebraic(cell.lower.value.root));
            }
            return {{}, false};
        case CellKind::FullLine:
            if (seed.has_value()) {
                return {RealAlg::fromRational(*seed), true};
            }
            return {RealAlg::fromRational(mpq_class(0)), true};
    }
    return {{}, false};
}

SampleHeuristicResult SampleHeuristic::pickSector(
    VarId /*var*/,
    const Bound& lower,
    const Bound& upper,
    const std::optional<mpq_class>& seed) {

    // Strategy: try seed if provided and in range, otherwise try 0, otherwise midpoint.
    if (seed.has_value()) {
        mpq_class q = *seed;
        // Check if seed is within bounds (simplified rational check)
        bool aboveLower = lower.isNegInf();
        bool belowUpper = upper.isPosInf();
        if (!aboveLower && lower.isRational()) {
            aboveLower = (lower.open ? q > lower.value.rational : q >= lower.value.rational);
        }
        if (!belowUpper && upper.isRational()) {
            belowUpper = (upper.open ? q < upper.value.rational : q <= upper.value.rational);
        }
        if (aboveLower && belowUpper) {
            return {RealAlg::fromRational(q), true};
        }
    }

    // Try 0
    bool zeroInRange = true;
    if (!lower.isNegInf()) {
        if (lower.isRational()) {
            zeroInRange = lower.open ? mpq_class(0) > lower.value.rational : mpq_class(0) >= lower.value.rational;
        } else {
            zeroInRange = false; // algebraic lower bound, can't easily check
        }
    }
    if (!upper.isPosInf() && zeroInRange) {
        if (upper.isRational()) {
            zeroInRange = upper.open ? mpq_class(0) < upper.value.rational : mpq_class(0) <= upper.value.rational;
        } else {
            zeroInRange = false;
        }
    }
    if (zeroInRange) {
        return {RealAlg::fromRational(mpq_class(0)), true};
    }

    // Fallback: try a small positive or negative rational
    if (!lower.isNegInf() && lower.isRational()) {
        mpq_class candidate = lower.value.rational + mpq_class(1);
        if (upper.isPosInf()) {
            return {RealAlg::fromRational(candidate), true};
        }
        if (upper.isRational() && candidate < upper.value.rational) {
            return {RealAlg::fromRational(candidate), true};
        }
    }
    if (!upper.isPosInf() && upper.isRational()) {
        mpq_class candidate = upper.value.rational - mpq_class(1);
        if (lower.isNegInf() || (lower.isRational() && candidate > lower.value.rational)) {
            return {RealAlg::fromRational(candidate), true};
        }
    }

    return {{}, false};
}

SampleHeuristicResult SampleHeuristic::pickSection(
    VarId /*var*/,
    const RealAlg& root) {
    return {root, true};
}

} // namespace nlcolver
