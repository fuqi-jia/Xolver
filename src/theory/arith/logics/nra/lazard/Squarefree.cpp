#include "theory/arith/logics/nra/lazard/Squarefree.h"
#include "theory/arith/logics/nra/preprocess/GcdEngine.h"
#include "theory/arith/logics/nra/lazard/LocalProjection.h"  // resultant()
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "util/EnvParam.h"   // XOLVER_NRA_LAZARD_MAX_COEFF_BITS projection firewall
#include <vector>

namespace xolver {

namespace {

// Projection coefficient firewall (crash fix). The Lazard projection of a
// high-degree mod-2^k system (QF_UFNRA sqrtmodinv-hoenicke modInvFull et al.)
// grows the gcd operands until libpoly's gcd / coefficient_add OOMs (~3.46 GB →
// SIGSEGV in coefficient_construct_copy) or corrupts the heap (glibc SIGABRT) —
// NEITHER catchable by the sigsetjmp harness, and BELOW the 262144-bit
// root-isolation cap. Refuse a gcd whose operand carries a coefficient past
// XOLVER_NRA_LAZARD_MAX_COEFF_BITS (default 65536) BEFORE the libpoly conversion.
// Scoped to the projection's exact-gcd path so the broadly-used toPrimitiveInteger
// keeps its high cap (the polynomial-stress suite needs >65536-bit conversions).
// complete=false → squarefree/projection incomplete → CDCAC Unknown: a clean
// caught unknown, never a wrong verdict and never the 44s/3.46 GB blowup.
bool projectionCoeffExceedsCap(const RationalPolynomial& p) {
    static const long capBits = [] {
        int v = env::paramInt("XOLVER_NRA_LAZARD_MAX_COEFF_BITS", 65536);
        return v > 0 ? static_cast<long>(v) : 65536L;
    }();
    // Measure the DENOMINATOR-CLEARED integer coefficients that toPrimitiveInteger
    // actually hands to libpoly (num * LCM/den) — NOT the raw rationals. modInvFull
    // has moderate num/den but coprime denominators, so the LCM blows the cleared
    // coeffs past the cap even though no single rational does. Replicates
    // toPrimitiveInteger Step 1-2 (the GCD reduction in Step 4 only shrinks, so
    // this is a sound — never under — estimate).
    mpz_class D = 1;
    for (const auto& [key, coeff] : p.terms()) {
        (void)key;
        const mpz_class den = coeff.get_den();
        if (den > 1) {
            mpz_class t;
            mpz_lcm(t.get_mpz_t(), D.get_mpz_t(), den.get_mpz_t());
            D = t;
        }
    }
    for (const auto& [key, coeff] : p.terms()) {
        (void)key;
        const mpz_class cleared = coeff.get_num() * (D / coeff.get_den());
        if (cleared != 0 &&
            static_cast<long>(mpz_sizeinbase(cleared.get_mpz_t(), 2)) > capBits)
            return true;
    }
    return false;
}

// --- Fast UNIVARIATE squarefree part over Q (avoids the O(n!) cofactor
// `resultant`/determinant path, which blows up on degree >= ~6). Used whenever
// the input is univariate in v; mathematically identical (squarefree part up to
// a unit), just computed by the Euclidean algorithm in O(deg^2). ---
using UniQ = std::vector<mpq_class>;   // coeff[i] = coefficient of v^i
int uDeg(const UniQ& a) { for (int i = (int)a.size() - 1; i >= 0; --i) if (a[i] != 0) return i; return -1; }
void uTrim(UniQ& a) { int d = uDeg(a); a.resize(d < 0 ? 0 : d + 1); }
UniQ uDeriv(const UniQ& a) { UniQ d; for (int i = 1; i < (int)a.size(); ++i) d.push_back(a[i] * i); uTrim(d); return d; }
UniQ uRem(UniQ a, const UniQ& b) {
    int db = uDeg(b);
    while (true) { int da = uDeg(a); if (da < db) break;
        mpq_class f = a[da] / b[db];
        for (int i = 0; i <= db; ++i) a[da - db + i] -= f * b[i];
        a[da] = 0; uTrim(a); if (a.empty()) break; }
    uTrim(a); return a;
}
UniQ uGcd(UniQ a, UniQ b) {
    while (uDeg(b) >= 0) { UniQ r = uRem(a, b); a = std::move(b); b = std::move(r); }
    if (uDeg(a) >= 0) { mpq_class l = a[uDeg(a)]; for (auto& c : a) c /= l; }   // monic
    return a;
}
UniQ uDiv(UniQ a, const UniQ& g) {
    int dg = uDeg(g); UniQ q(std::max(0, uDeg(a) - dg + 1), mpq_class(0));
    while (true) { int da = uDeg(a); if (da < dg) break;
        mpq_class f = a[da] / g[dg]; q[da - dg] = f;
        for (int i = 0; i <= dg; ++i) a[da - dg + i] -= f * g[i];
        a[da] = 0; uTrim(a); if (a.empty()) break; }
    return q;
}

// squarefree part of a univariate (in v) RationalPolynomial, monic-normalized.
RationalPolynomial univariateSquarefreePart(const RationalPolynomial& p, VarId v) {
    auto coeffs = p.coefficients(v);            // index i = coeff of v^i (constant polys)
    UniQ a(coeffs.size(), mpq_class(0));
    for (size_t i = 0; i < coeffs.size(); ++i) {
        RationalPolynomial c = coeffs[i]; c.normalize();
        a[i] = c.isZero() ? mpq_class(0) : c.constantValue();
    }
    uTrim(a);
    UniQ g = uGcd(a, uDeriv(a));
    UniQ sf = (uDeg(g) >= 1) ? uDiv(a, g) : a;
    uTrim(sf);
    // make monic, rebuild as RationalPolynomial
    if (uDeg(sf) >= 0) { mpq_class l = sf[uDeg(sf)]; for (auto& c : sf) c /= l; }
    RationalPolynomial out;
    for (int i = 0; i < (int)sf.size(); ++i) {
        if (sf[i] == 0) continue;
        if (i == 0) out.addConstant(sf[i]); else out.addVar(v, i, sf[i]);
    }
    out.normalize();
    return out;
}

// Divide by the coefficient of the largest monomial (terms() is sorted by
// MonomialKey, so rbegin() is the largest). Matches ProjectionClosure::intern.
RationalPolynomial normalizeUpToUnit(const RationalPolynomial& p) {
    if (p.isZero()) return p;
    const auto& terms = p.terms();
    mpq_class lead = terms.rbegin()->second;
    if (lead == 0 || lead == 1) return p;
    RationalPolynomial r = p;
    r *= (mpq_class(1) / lead);
    r.normalize();
    return r;
}

// EXACT multivariate gcd of a and b via libpoly (PolynomialKernel::gcd), with
// MANDATORY exactDivide verification. Returns {gcd, true} only when libpoly's
// gcd both round-trips back to a RationalPolynomial AND exactly divides BOTH a
// and b (so it is a verified common divisor). Any failure (kernel unsupported,
// conversion failure, exactDivide disagreement) returns complete=false so the
// caller falls back / marks the closure incomplete — never an unverified gcd.
//
// Soundness: even if libpoly's gcd were not maximal, exactDivide guarantees it
// is a genuine common divisor; the squarefree/content path only needs an exact
// common-divisor division, and the up-to-rational-unit normalization (intern's
// canonicalKey) absorbs any scale difference. A wrong (non-dividing) result is
// rejected by exactDivide.
SquarefreeResult gcdTwoExact(const RationalPolynomial& a, const RationalPolynomial& b,
                             PolynomialKernel& kernel) {
    if (a.isZero()) return {b, true};
    if (b.isZero()) return {a, true};
    if (a.isConstant() || b.isConstant())
        return {RationalPolynomial::fromConstant(mpq_class(1)), true};

    // Projection coefficient firewall: refuse runaway mod-2^k operands BEFORE the
    // libpoly conversion/gcd (see projectionCoeffExceedsCap). complete=false →
    // closure incomplete → CDCAC Unknown.
    if (projectionCoeffExceedsCap(a) || projectionCoeffExceedsCap(b))
        return {RationalPolynomial::fromConstant(mpq_class(1)), false};

    // RP -> integer-primitive PolyId (clears denominators; positive scale,
    // benign — same conversion as the proven PSC path).
    auto aNorm = a.toPrimitiveInteger(kernel);
    auto bNorm = b.toPrimitiveInteger(kernel);
    if (!aNorm.ok() || !bNorm.ok()) return {RationalPolynomial::fromConstant(mpq_class(1)), false};

    PolyId gId = kernel.gcd(aNorm.poly, bNorm.poly);
    if (gId == NullPoly) return {RationalPolynomial::fromConstant(mpq_class(1)), false};

    auto gOpt = RationalPolynomial::fromPolyId(gId, kernel);
    if (!gOpt) return {RationalPolynomial::fromConstant(mpq_class(1)), false};
    RationalPolynomial g = std::move(*gOpt);
    g.normalize();
    if (g.isZero()) return {RationalPolynomial::fromConstant(mpq_class(1)), false};
    if (g.isConstant()) return {RationalPolynomial::fromConstant(mpq_class(1)), true};

    // MANDATORY verification: g must exactly divide BOTH a and b in Q[X].
    if (!GcdEngine::exactDivide(a, g)) return {RationalPolynomial::fromConstant(mpq_class(1)), false};
    if (!GcdEngine::exactDivide(b, g)) return {RationalPolynomial::fromConstant(mpq_class(1)), false};

    return {g, true};
}

// gcd over Q[X] of two polynomials in the lower variables (no main-var here).
// A nonzero constant operand makes the gcd a unit (1). complete=false on a
// non-exact subresultant gcd. When `kernel != nullptr` routes through the
// EXACT libpoly gcd above; otherwise the hand-rolled subresultant PRS.
SquarefreeResult gcdTwo(const RationalPolynomial& a, const RationalPolynomial& b,
                        PolynomialKernel* kernel = nullptr) {
    if (a.isZero()) return {b, true};
    if (b.isZero()) return {a, true};
    if (a.isConstant() || b.isConstant())
        return {RationalPolynomial::fromConstant(mpq_class(1)), true};

    if (kernel != nullptr) return gcdTwoExact(a, b, *kernel);

    VarId v = NullVar;
    for (VarId x : a.variables()) v = (v == NullVar || x > v) ? x : v;
    for (VarId x : b.variables()) v = (v == NullVar || x > v) ? x : v;

    auto r = GcdEngine::gcdCandidateBySubresultant(a, b, v);
    if (!r.exact) return {RationalPolynomial::fromConstant(mpq_class(1)), false};
    return {r.gcd, true};
}

}  // namespace

SquarefreeResult contentWrt(const RationalPolynomial& p, VarId v, PolynomialKernel* kernel) {
    if (p.isZero()) return {RationalPolynomial::fromConstant(mpq_class(0)), true};

    auto coeffs = p.coefficients(v);  // index i = coefficient of v^i
    RationalPolynomial acc;
    bool started = false;
    for (auto& c : coeffs) {
        if (c.isZero()) continue;
        if (!started) { acc = c; started = true; continue; }
        auto g = gcdTwo(acc, c, kernel);
        if (!g.complete) return {RationalPolynomial::fromConstant(mpq_class(1)), false};
        acc = g.poly;
        if (acc.isConstant()) break;  // gcd is a unit => content 1
    }
    if (!started) return {RationalPolynomial::fromConstant(mpq_class(0)), true};
    if (acc.isConstant()) return {RationalPolynomial::fromConstant(mpq_class(1)), true};
    return {normalizeUpToUnit(acc), true};
}

SquarefreeResult primitivePartWrt(const RationalPolynomial& p, VarId v, PolynomialKernel* kernel) {
    if (p.isZero()) return {p, true};
    auto c = contentWrt(p, v, kernel);
    if (!c.complete) return {p, false};
    if (c.poly.isZero() || c.poly.isConstant())
        return {normalizeUpToUnit(p), true};
    auto q = GcdEngine::exactDivide(p, c.poly);
    if (!q) return {p, false};
    return {normalizeUpToUnit(*q), true};
}

SquarefreeResult squarefreePartWrt(const RationalPolynomial& p, VarId v, PolynomialKernel* kernel) {
    auto pp = primitivePartWrt(p, v, kernel);
    if (!pp.complete) return {p, false};
    RationalPolynomial base = pp.poly;
    if (base.degree(v) <= 0) return {base, true};  // constant in v => squarefree

    // Fast univariate path: when `base` involves only v, the multivariate
    // resultant/determinant below is O(deg!) and explodes past ~deg 6. The
    // univariate squarefree part is the same up to a unit, computed in O(deg^2).
    {
        bool univariate = true;
        for (VarId x : base.variables()) if (x != v) { univariate = false; break; }
        if (univariate) return {univariateSquarefreePart(base, v), true};
    }

    RationalPolynomial d = base.derivative(v);
    if (d.isZero()) return {base, true};

    // EXACT libpoly path: gcd_v(base, base') via the verified kernel gcd, then
    // squarefreePart = base / gcd. The gcd is already exactDivide-verified to
    // divide `base` inside gcdTwoExact; we divide once more here for the quotient
    // (a divisor of base, so guaranteed exact). A unit gcd ⇒ already squarefree.
    if (kernel != nullptr) {
        auto g = gcdTwo(base, d, kernel);
        if (!g.complete) return {base, false};
        if (g.poly.isZero() || g.poly.isConstant() || g.poly.degree(v) < 1)
            return {base, true};   // gcd is a unit in v ⇒ base already squarefree
        auto q = GcdEngine::exactDivide(base, g.poly);
        if (!q) return {base, false};
        return {normalizeUpToUnit(*q), true};
    }

    // Coprimeness via the resultant: res(base, base') != 0 ⟺ base is squarefree
    // (no repeated factor). This is reliable for both univariate and
    // multivariate inputs; the multivariate subresultant gcd below degenerates
    // on purely-univariate coprime inputs, so we MUST gate on the resultant
    // first and only invoke the gcd division when a repeated factor is present.
    RationalPolynomial res = resultant(base, d, v);
    res.normalize();
    if (!res.isZero()) return {base, true};  // squarefree already

    auto r = GcdEngine::gcdCandidateBySubresultant(base, d, v);
    if (!r.exact) return {base, false};
    // squarefreePart = base / gcd_v(base, base') = pQuot (up to unit).
    return {normalizeUpToUnit(r.pQuot), true};
}

}  // namespace xolver
