#include "theory/arith/nra/nla/NlaCutGenerator.h"

namespace xolver {
namespace nla {

namespace {

std::vector<SatLit> unionReasons(const std::vector<SatLit>& a,
                                  const std::vector<SatLit>& b) {
    std::vector<SatLit> out = a;
    out.reserve(a.size() + b.size());
    for (const SatLit& r : b) {
        bool dup = false;
        for (const SatLit& q : out) {
            if (q == r) { dup = true; break; }
        }
        if (!dup) out.push_back(r);
    }
    return out;
}

} // namespace

NlaCutGenerator::NlaCutGenerator(PolynomialKernel& kernel)
    : kernel_(kernel) {}

std::vector<NlaCut> NlaCutGenerator::monotonicityProduct(
        const VarInterval& xInt, const VarInterval& yInt) {
    std::vector<NlaCut> cuts;
    if (xInt.varPoly == NullPoly || yInt.varPoly == NullPoly) return cuts;

    // Lo cut: requires both lower bounds present and both >= 0.
    // Derivation: x >= lo_x >= 0 ∧ y >= lo_y >= 0 ⇒ x*y >= lo_x * lo_y
    //   (multiply x ≥ lo_x by y ≥ 0 → x·y ≥ lo_x·y, then lo_x·y ≥ lo_x·lo_y
    //    via lo_x ≥ 0 and y ≥ lo_y). Sound for any non-negative quadrant.
    if (xInt.lo && yInt.lo && *xInt.lo >= 0 && *yInt.lo >= 0) {
        PolyId xy = kernel_.mul(xInt.varPoly, yInt.varPoly);
        mpq_class loProduct = *xInt.lo * *yInt.lo;
        PolyId loConst = kernel_.mkConst(loProduct);
        // cut poly: x*y - lo_x*lo_y, rel = Geq → x*y >= lo_x*lo_y
        PolyId cutPoly = kernel_.sub(xy, loConst);
        NlaCut cut;
        cut.kind = NlaCutKind::Monotonicity;
        cut.poly = cutPoly;
        cut.rel = Relation::Geq;
        cut.reasons = unionReasons(xInt.reasons, yInt.reasons);
        cuts.push_back(std::move(cut));
    }

    // Hi cut: requires both lower bounds non-negative (so the product is
    // monotonically increasing on the rectangle [lo_x, hi_x]×[lo_y, hi_y])
    // and both upper bounds present.
    // Derivation: x ≤ hi_x ∧ y ≤ hi_y ∧ x,y ≥ 0
    //          ⇒ x*y ≤ hi_x*y ≤ hi_x*hi_y.
    if (xInt.lo && yInt.lo && *xInt.lo >= 0 && *yInt.lo >= 0
        && xInt.hi && yInt.hi) {
        PolyId xy = kernel_.mul(xInt.varPoly, yInt.varPoly);
        mpq_class hiProduct = *xInt.hi * *yInt.hi;
        PolyId hiConst = kernel_.mkConst(hiProduct);
        // cut poly: hi_x*hi_y - x*y, rel = Geq → hi_x*hi_y >= x*y
        PolyId cutPoly = kernel_.sub(hiConst, xy);
        NlaCut cut;
        cut.kind = NlaCutKind::Monotonicity;
        cut.poly = cutPoly;
        cut.rel = Relation::Geq;
        cut.reasons = unionReasons(xInt.reasons, yInt.reasons);
        cuts.push_back(std::move(cut));
    }

    return cuts;
}

std::vector<NlaCut> NlaCutGenerator::monotonicitySquare(
        const VarInterval& xInt) {
    std::vector<NlaCut> cuts;
    if (xInt.varPoly == NullPoly) return cuts;

    // We emit `x*x` cuts whenever we can pin the lower/upper bound on x^2
    // soundly from the interval [lo, hi].
    //
    // Min(x^2) on [lo, hi] =
    //   lo^2         if lo >= 0   (square increasing on the interval)
    //   hi^2         if hi <= 0   (square decreasing on the interval)
    //   0            if 0 ∈ [lo, hi]
    //
    // Max(x^2) on [lo, hi] = max(lo^2, hi^2)  (require both bounds).
    PolyId xx = kernel_.mul(xInt.varPoly, xInt.varPoly);

    // Lo cut: x*x - minSq >= 0.
    {
        std::optional<mpq_class> minSq;
        if (xInt.lo && *xInt.lo >= 0) {
            minSq = (*xInt.lo) * (*xInt.lo);
        } else if (xInt.hi && *xInt.hi <= 0) {
            minSq = (*xInt.hi) * (*xInt.hi);
        } else if (xInt.lo && xInt.hi && *xInt.lo <= 0 && *xInt.hi >= 0) {
            // 0 in [lo, hi] — the trivial floor is 0, which is the
            // unconditional fact x^2 >= 0 (true everywhere). Emit it: it
            // still carries the interval's reason set, but the cut adds no
            // information beyond what every solver already has, so callers
            // may filter. We include it for completeness so the test suite
            // can pin all branches of this function.
            minSq = mpq_class(0);
        }
        if (minSq) {
            PolyId loConst = kernel_.mkConst(*minSq);
            PolyId cutPoly = kernel_.sub(xx, loConst);
            NlaCut cut;
            cut.kind = NlaCutKind::Monotonicity;
            cut.poly = cutPoly;
            cut.rel = Relation::Geq;
            cut.reasons = xInt.reasons;
            cuts.push_back(std::move(cut));
        }
    }

    // Hi cut: maxSq - x*x >= 0 (requires both bounds).
    if (xInt.lo && xInt.hi) {
        mpq_class loSq = (*xInt.lo) * (*xInt.lo);
        mpq_class hiSq = (*xInt.hi) * (*xInt.hi);
        mpq_class maxSq = (loSq > hiSq) ? loSq : hiSq;
        PolyId hiConst = kernel_.mkConst(maxSq);
        PolyId cutPoly = kernel_.sub(hiConst, xx);
        NlaCut cut;
        cut.kind = NlaCutKind::Monotonicity;
        cut.poly = cutPoly;
        cut.rel = Relation::Geq;
        cut.reasons = xInt.reasons;
        cuts.push_back(std::move(cut));
    }

    return cuts;
}

NlaCut NlaCutGenerator::tangentSquare(PolyId xPoly,
                                       const mpq_class& modelPoint,
                                       const std::vector<SatLit>& reasons) {
    // Cut polynomial: x^2 - 2*m*x + m^2 = (x - m)^2 >= 0.
    // Mathematically a sum-of-squares — sound for any (m, x).
    PolyId xx = kernel_.mul(xPoly, xPoly);
    mpq_class twoM = mpq_class(2) * modelPoint;
    mpq_class mSq = modelPoint * modelPoint;
    PolyId twoMx = kernel_.mul(kernel_.mkConst(twoM), xPoly);
    PolyId xxMinus2mx = kernel_.sub(xx, twoMx);
    PolyId cutPoly = kernel_.add(xxMinus2mx, kernel_.mkConst(mSq));
    NlaCut cut;
    cut.kind = NlaCutKind::Tangent;
    cut.poly = cutPoly;
    cut.rel = Relation::Geq;
    cut.reasons = reasons;
    return cut;
}

std::optional<NlaCut> NlaCutGenerator::proportionalMultiply(
        PolyId lhsPoly, PolyId rhsPoly, SatLit atomReason,
        const VarInterval& zInt) {
    if (lhsPoly == NullPoly || rhsPoly == NullPoly ||
        zInt.varPoly == NullPoly) return std::nullopt;
    // Soundness precondition: z >= 0 along the entire interval, otherwise
    // multiplying flips the inequality direction (or breaks it at z = 0).
    if (!zInt.lo || *zInt.lo < 0) return std::nullopt;

    // Cut: rhs*z - lhs*z >= 0, i.e. lhs*z <= rhs*z.
    PolyId rhsZ = kernel_.mul(rhsPoly, zInt.varPoly);
    PolyId lhsZ = kernel_.mul(lhsPoly, zInt.varPoly);
    PolyId cutPoly = kernel_.sub(rhsZ, lhsZ);
    NlaCut cut;
    cut.kind = NlaCutKind::Proportional;
    cut.poly = cutPoly;
    cut.rel = Relation::Geq;
    cut.reasons = unionReasons({atomReason}, zInt.reasons);
    return cut;
}

std::vector<NlaCut> NlaCutGenerator::mccormickBilinear(
        const VarInterval& xInt, const VarInterval& yInt) {
    std::vector<NlaCut> cuts;
    if (xInt.varPoly == NullPoly || yInt.varPoly == NullPoly) return cuts;
    // All 4 cuts need all four bounds (lo_x, hi_x, lo_y, hi_y).
    if (!xInt.lo || !xInt.hi || !yInt.lo || !yInt.hi) return cuts;

    // Cut polynomials (each derived from `(x - bound_x) * (y - bound_y) >= 0`
    // or `<= 0`, expanded — those are sign-known products on a McCormick
    // rectangle):
    //
    //   (x - lo_x) * (y - lo_y) >= 0
    //   ⇔ x*y - lo_x*y - x*lo_y + lo_x*lo_y >= 0
    //   ⇔ x*y >= lo_x*y + x*lo_y - lo_x*lo_y
    //
    // Same for the other three corner choices. The cut polynomial is the
    // McCormick-form polynomial directly:
    //
    //   under: x*y - lo_x*y - x*lo_y + lo_x*lo_y >= 0
    //   under: x*y - hi_x*y - x*hi_y + hi_x*hi_y >= 0
    //   over:  hi_x*y + x*lo_y - hi_x*lo_y - x*y >= 0
    //   over:  lo_x*y + x*hi_y - lo_x*hi_y - x*y >= 0
    //
    // The two under-estimators are derived from squaring the same sign
    // (both factors non-negative OR both factors non-positive) which holds
    // OUTSIDE the rectangle too — but ON the rectangle they collectively
    // sandwich x*y. McCormick's classical result is that these jointly
    // form the convex hull of {(x, y, xy) : lo_x ≤ x ≤ hi_x,
    // lo_y ≤ y ≤ hi_y}. For Phase B we emit them all and let the LRA
    // propagator pick the tightest under each model.
    auto reasons = unionReasons(xInt.reasons, yInt.reasons);
    PolyId xy = kernel_.mul(xInt.varPoly, yInt.varPoly);

    auto emit = [&](PolyId polyMinusXy, bool over) {
        // polyMinusXy is `(bound_x*y + x*bound_y - bound_x*bound_y)`.
        // Under: x*y - polyMinusXy >= 0
        // Over:  polyMinusXy - x*y >= 0
        PolyId cutPoly = over
            ? kernel_.sub(polyMinusXy, xy)
            : kernel_.sub(xy, polyMinusXy);
        NlaCut cut;
        cut.kind = NlaCutKind::Tangent;  // McCormick is the bilinear
                                          // tangent envelope family.
        cut.poly = cutPoly;
        cut.rel = Relation::Geq;
        cut.reasons = reasons;
        cuts.push_back(std::move(cut));
    };

    auto buildCorner = [&](const mpq_class& bx, const mpq_class& by) {
        // Returns `bx*y + x*by - bx*by` as a PolyId.
        PolyId bxY = kernel_.mul(kernel_.mkConst(bx), yInt.varPoly);
        PolyId xBy = kernel_.mul(xInt.varPoly, kernel_.mkConst(by));
        PolyId bxBy = kernel_.mkConst(bx * by);
        return kernel_.sub(kernel_.add(bxY, xBy), bxBy);
    };

    emit(buildCorner(*xInt.lo, *yInt.lo), /*over=*/false);
    emit(buildCorner(*xInt.hi, *yInt.hi), /*over=*/false);
    emit(buildCorner(*xInt.hi, *yInt.lo), /*over=*/true);
    emit(buildCorner(*xInt.lo, *yInt.hi), /*over=*/true);

    return cuts;
}

} // namespace nla
} // namespace xolver
