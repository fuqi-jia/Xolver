#include "theory/arith/nra/projection/Squarefree.h"
#include "theory/arith/nra/preprocess/GcdEngine.h"
#include "theory/arith/nra/projection/LocalProjection.h"  // resultant()
#include <vector>

namespace zolver {

namespace {

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

}  // namespace zolver
