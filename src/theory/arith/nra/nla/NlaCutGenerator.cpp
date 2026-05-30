#include "theory/arith/nra/nla/NlaCutGenerator.h"

namespace xolver {
namespace nla {

namespace {

// Polynomial kernels backed by libpoly only accept integer-coefficient
// polynomials — `mkConst(q)` returns NullPoly when q has a non-trivial
// denominator. Cut polynomials computed from rational interval bounds
// (e.g. lo² for lo = 9/10 ⇒ 81/100) must therefore be scaled before
// being constructed. This helper returns the integer numerator for an
// mpq, the multiplier that converts the original cut to the scaled
// integer form, and a guard for the "already integer" fast path.
//
// For a cut shape `LHS - q ≥ 0` with q ∈ Q, scaling by den(q) yields
// `den(q)·LHS - num(q) ≥ 0` which is sound because den(q) > 0 (multi-
// plying both sides of an inequality by a positive quantity preserves
// direction). The cut polynomial then contains only integer-coefficient
// terms, which libpoly accepts.
struct ScaledRational { mpz_class num; mpz_class den; };
ScaledRational scaleParts(const mpq_class& q) {
    return { q.get_num(), q.get_den() };
}

// Multiply `p` by a positive integer scalar `s`. Returns p unchanged
// when s == 1 (no-op fast path). NullPoly-propagating: if either
// operand is NullPoly the result is too.
PolyId scaleByInt(PolynomialKernel& k, PolyId p, const mpz_class& s) {
    if (s == 1) return p;
    if (p == NullPoly) return NullPoly;
    PolyId sPoly = k.mkConst(mpq_class(s));
    if (sPoly == NullPoly) return NullPoly;
    return k.mul(sPoly, p);
}

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
        if (xy != NullPoly) {
            mpq_class loProduct = *xInt.lo * *yInt.lo;
            auto sp = scaleParts(loProduct);
            PolyId loConst = kernel_.mkConst(mpq_class(sp.num));
            PolyId scaledXy = scaleByInt(kernel_, xy, sp.den);
            if (loConst != NullPoly && scaledXy != NullPoly) {
                PolyId cutPoly = kernel_.sub(scaledXy, loConst);
                if (cutPoly != NullPoly) {
                    NlaCut cut;
                    cut.kind = NlaCutKind::Monotonicity;
                    cut.poly = cutPoly;
                    cut.rel = Relation::Geq;
                    cut.reasons = unionReasons(xInt.reasons, yInt.reasons);
                    cuts.push_back(std::move(cut));
                }
            }
        }
    }

    // Hi cut: requires both lower bounds non-negative (so the product is
    // monotonically increasing on the rectangle [lo_x, hi_x]×[lo_y, hi_y])
    // and both upper bounds present.
    // Derivation: x ≤ hi_x ∧ y ≤ hi_y ∧ x,y ≥ 0
    //          ⇒ x*y ≤ hi_x*y ≤ hi_x*hi_y.
    if (xInt.lo && yInt.lo && *xInt.lo >= 0 && *yInt.lo >= 0
        && xInt.hi && yInt.hi) {
        PolyId xy = kernel_.mul(xInt.varPoly, yInt.varPoly);
        if (xy != NullPoly) {
            mpq_class hiProduct = *xInt.hi * *yInt.hi;
            auto sp = scaleParts(hiProduct);
            PolyId hiConst = kernel_.mkConst(mpq_class(sp.num));
            PolyId scaledXy = scaleByInt(kernel_, xy, sp.den);
            if (hiConst != NullPoly && scaledXy != NullPoly) {
                PolyId cutPoly = kernel_.sub(hiConst, scaledXy);
                if (cutPoly != NullPoly) {
                    NlaCut cut;
                    cut.kind = NlaCutKind::Monotonicity;
                    cut.poly = cutPoly;
                    cut.rel = Relation::Geq;
                    cut.reasons = unionReasons(xInt.reasons, yInt.reasons);
                    cuts.push_back(std::move(cut));
                }
            }
        }
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
    if (xx == NullPoly) return cuts;

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
            // Scale to integer-coefficient form: `xx - minSq >= 0` becomes
            // `den(minSq) * xx - num(minSq) >= 0`. Sound: den > 0.
            auto sp = scaleParts(*minSq);
            PolyId scaledXx = scaleByInt(kernel_, xx, sp.den);
            PolyId constPoly = kernel_.mkConst(mpq_class(sp.num));
            if (scaledXx == NullPoly || constPoly == NullPoly) {
                // Kernel rejected — bail this cut (sound: skip rather than
                // emit an invalid PolyId).
            } else {
                PolyId cutPoly = kernel_.sub(scaledXx, constPoly);
                if (cutPoly != NullPoly) {
                    NlaCut cut;
                    cut.kind = NlaCutKind::Monotonicity;
                    cut.poly = cutPoly;
                    cut.rel = Relation::Geq;
                    cut.reasons = xInt.reasons;
                    cuts.push_back(std::move(cut));
                }
            }
        }
    }

    // Hi cut: maxSq - x*x >= 0 (requires both bounds). Scale-to-integer
    // identical to the lo branch.
    if (xInt.lo && xInt.hi) {
        mpq_class loSq = (*xInt.lo) * (*xInt.lo);
        mpq_class hiSq = (*xInt.hi) * (*xInt.hi);
        mpq_class maxSq = (loSq > hiSq) ? loSq : hiSq;
        auto sp = scaleParts(maxSq);
        PolyId constPoly = kernel_.mkConst(mpq_class(sp.num));
        PolyId scaledXx = scaleByInt(kernel_, xx, sp.den);
        if (constPoly != NullPoly && scaledXx != NullPoly) {
            PolyId cutPoly = kernel_.sub(constPoly, scaledXx);
            if (cutPoly != NullPoly) {
                NlaCut cut;
                cut.kind = NlaCutKind::Monotonicity;
                cut.poly = cutPoly;
                cut.rel = Relation::Geq;
                cut.reasons = xInt.reasons;
                cuts.push_back(std::move(cut));
            }
        }
    }

    return cuts;
}

NlaCut NlaCutGenerator::tangentSquare(PolyId xPoly,
                                       const mpq_class& modelPoint,
                                       const std::vector<SatLit>& reasons) {
    // Cut polynomial: (x - m)^2 >= 0 = x^2 - 2*m*x + m^2.
    // For rational m = p/q, scale by q^2 to get integer coefficients:
    //   q^2 * x^2 - 2*p*q * x + p^2 >= 0
    // Sound: q^2 > 0, multiplying preserves direction. Always emittable
    // as long as the kernel accepts integer-coefficient polynomials.
    NlaCut cut;
    cut.kind = NlaCutKind::Tangent;
    cut.rel = Relation::Geq;
    cut.reasons = reasons;
    cut.poly = NullPoly;

    auto sp = scaleParts(modelPoint);
    mpz_class q  = sp.den;
    mpz_class p  = sp.num;
    mpz_class q2 = q * q;
    mpz_class pq2 = 2 * p * q;
    mpz_class p2 = p * p;

    PolyId xx = kernel_.mul(xPoly, xPoly);
    if (xx == NullPoly) return cut;
    PolyId scaledXx = scaleByInt(kernel_, xx, q2);
    PolyId twoPqPoly = kernel_.mkConst(mpq_class(pq2));
    PolyId twoPqX = (twoPqPoly == NullPoly) ? NullPoly : kernel_.mul(twoPqPoly, xPoly);
    PolyId p2Poly = kernel_.mkConst(mpq_class(p2));
    if (scaledXx == NullPoly || twoPqX == NullPoly || p2Poly == NullPoly) return cut;
    PolyId tmp = kernel_.sub(scaledXx, twoPqX);
    if (tmp == NullPoly) return cut;
    cut.poly = kernel_.add(tmp, p2Poly);
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
    if (rhsZ == NullPoly || lhsZ == NullPoly) return std::nullopt;
    PolyId cutPoly = kernel_.sub(rhsZ, lhsZ);
    if (cutPoly == NullPoly) return std::nullopt;
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
    if (xy == NullPoly) return cuts;

    auto emit = [&](PolyId polyMinusXy, bool over) {
        // polyMinusXy is `(bound_x*y + x*bound_y - bound_x*bound_y)`.
        // Under: x*y - polyMinusXy >= 0
        // Over:  polyMinusXy - x*y >= 0
        PolyId cutPoly = over
            ? kernel_.sub(polyMinusXy, xy)
            : kernel_.sub(xy, polyMinusXy);
        if (cutPoly == NullPoly) return;
        NlaCut cut;
        cut.kind = NlaCutKind::Tangent;  // McCormick is the bilinear
                                          // tangent envelope family.
        cut.poly = cutPoly;
        cut.rel = Relation::Geq;
        cut.reasons = reasons;
        cuts.push_back(std::move(cut));
    };

    auto buildCorner = [&](const mpq_class& bx, const mpq_class& by) -> PolyId {
        // Returns `bx*y + x*by - bx*by` as a PolyId. NullPoly if any
        // sub-step rejects (e.g. mkConst of a non-integer rational).
        // McCormick cuts with rational bounds need full scaling (TBD);
        // for now, gracefully skip non-integer corners.
        PolyId bxPoly = kernel_.mkConst(bx);
        PolyId byPoly = kernel_.mkConst(by);
        PolyId bxByPoly = kernel_.mkConst(bx * by);
        if (bxPoly == NullPoly || byPoly == NullPoly || bxByPoly == NullPoly)
            return NullPoly;
        PolyId bxY = kernel_.mul(bxPoly, yInt.varPoly);
        PolyId xBy = kernel_.mul(xInt.varPoly, byPoly);
        if (bxY == NullPoly || xBy == NullPoly) return NullPoly;
        PolyId sum = kernel_.add(bxY, xBy);
        if (sum == NullPoly) return NullPoly;
        return kernel_.sub(sum, bxByPoly);
    };

    auto safeEmit = [&](PolyId corner, bool over) {
        if (corner == NullPoly) return;
        emit(corner, over);
    };
    safeEmit(buildCorner(*xInt.lo, *yInt.lo), /*over=*/false);
    safeEmit(buildCorner(*xInt.hi, *yInt.hi), /*over=*/false);
    safeEmit(buildCorner(*xInt.hi, *yInt.lo), /*over=*/true);
    safeEmit(buildCorner(*xInt.lo, *yInt.hi), /*over=*/true);

    return cuts;
}

} // namespace nla
} // namespace xolver
