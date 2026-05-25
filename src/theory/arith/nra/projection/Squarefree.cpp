#include "theory/arith/nra/projection/Squarefree.h"
#include "theory/arith/nra/preprocess/GcdEngine.h"
#include "theory/arith/nra/projection/LocalProjection.h"  // resultant()

namespace nlcolver {

namespace {

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

// gcd over Q[X] of two polynomials in the lower variables (no main-var here).
// A nonzero constant operand makes the gcd a unit (1). complete=false on a
// non-exact subresultant gcd.
SquarefreeResult gcdTwo(const RationalPolynomial& a, const RationalPolynomial& b) {
    if (a.isZero()) return {b, true};
    if (b.isZero()) return {a, true};
    if (a.isConstant() || b.isConstant())
        return {RationalPolynomial::fromConstant(mpq_class(1)), true};

    VarId v = NullVar;
    for (VarId x : a.variables()) v = (v == NullVar || x > v) ? x : v;
    for (VarId x : b.variables()) v = (v == NullVar || x > v) ? x : v;

    auto r = GcdEngine::gcdCandidateBySubresultant(a, b, v);
    if (!r.exact) return {RationalPolynomial::fromConstant(mpq_class(1)), false};
    return {r.gcd, true};
}

}  // namespace

SquarefreeResult contentWrt(const RationalPolynomial& p, VarId v) {
    if (p.isZero()) return {RationalPolynomial::fromConstant(mpq_class(0)), true};

    auto coeffs = p.coefficients(v);  // index i = coefficient of v^i
    RationalPolynomial acc;
    bool started = false;
    for (auto& c : coeffs) {
        if (c.isZero()) continue;
        if (!started) { acc = c; started = true; continue; }
        auto g = gcdTwo(acc, c);
        if (!g.complete) return {RationalPolynomial::fromConstant(mpq_class(1)), false};
        acc = g.poly;
        if (acc.isConstant()) break;  // gcd is a unit => content 1
    }
    if (!started) return {RationalPolynomial::fromConstant(mpq_class(0)), true};
    if (acc.isConstant()) return {RationalPolynomial::fromConstant(mpq_class(1)), true};
    return {normalizeUpToUnit(acc), true};
}

SquarefreeResult primitivePartWrt(const RationalPolynomial& p, VarId v) {
    if (p.isZero()) return {p, true};
    auto c = contentWrt(p, v);
    if (!c.complete) return {p, false};
    if (c.poly.isZero() || c.poly.isConstant())
        return {normalizeUpToUnit(p), true};
    auto q = GcdEngine::exactDivide(p, c.poly);
    if (!q) return {p, false};
    return {normalizeUpToUnit(*q), true};
}

SquarefreeResult squarefreePartWrt(const RationalPolynomial& p, VarId v) {
    auto pp = primitivePartWrt(p, v);
    if (!pp.complete) return {p, false};
    RationalPolynomial base = pp.poly;
    if (base.degree(v) <= 0) return {base, true};  // constant in v => squarefree

    RationalPolynomial d = base.derivative(v);
    if (d.isZero()) return {base, true};

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

}  // namespace nlcolver
