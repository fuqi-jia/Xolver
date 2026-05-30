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

} // namespace nla
} // namespace xolver
