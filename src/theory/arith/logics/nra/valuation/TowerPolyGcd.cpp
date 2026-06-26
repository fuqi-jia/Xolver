#include "theory/arith/logics/nra/valuation/TowerPolyGcd.h"
#include <vector>

namespace xolver {

namespace {

// Univariate-in-t polynomial over K, as coeffs[i] = coefficient of t^i.
using KPoly = std::vector<TowerElement>;

int kdeg(const KPoly& a, const TowerKernel& K) {
    for (int i = static_cast<int>(a.size()) - 1; i >= 0; --i)
        if (!K.isZero(a[i])) return i;
    return -1;
}

KPoly toCoeffs(const RationalPolynomial& p, VarId t, const TowerKernel& K) {
    auto cs = p.coefficients(t);                 // each in extension vars
    KPoly out;
    out.reserve(cs.size());
    for (auto& c : cs) out.push_back(K.reduce(c));
    return out;
}

RationalPolynomial fromCoeffs(const KPoly& a, VarId t) {
    RationalPolynomial r;
    for (size_t i = 0; i < a.size(); ++i) {
        if (a[i].value.isZero()) continue;
        RationalPolynomial term = a[i].value;
        if (i > 0) term = term * RationalPolynomial::fromVar(t, static_cast<int>(i), mpq_class(1));
        r = r + term;
    }
    r.normalize();
    return r;
}

// Remainder of a divided by b over K (b != 0). ok=false if a leading inverse fails.
bool kRem(KPoly a, const KPoly& b, const TowerKernel& K, KPoly& out) {
    int db = kdeg(b, K);
    if (db < 0) return false;
    auto lcbInv = K.inverse(b[db]);
    if (!lcbInv) return false;
    int guard = 0;
    while (true) {
        int da = kdeg(a, K);
        if (da < db) break;
        if (++guard > 100000) return false;
        TowerElement factor = K.mul(a[da], *lcbInv);
        // a -= factor * t^(da-db) * b
        for (int i = 0; i <= db; ++i)
            a[da - db + i] = K.sub(a[da - db + i], K.mul(factor, b[i]));
        a[da] = K.fromRational(mpq_class(0));     // force-zero the top term
    }
    out = std::move(a);
    return true;
}

}  // namespace

TowerGcdResult towerPolyGcd(const RationalPolynomial& f, const RationalPolynomial& g,
                            VarId targetVar, const TowerKernel& K) {
    TowerGcdResult res;
    KPoly a = toCoeffs(f, targetVar, K);
    KPoly b = toCoeffs(g, targetVar, K);

    // Euclid: keep a as the running gcd, b as the divisor.
    int guard = 0;
    while (kdeg(b, K) >= 0) {
        if (++guard > 100000) { res.ok = false; return res; }
        KPoly r;
        if (!kRem(a, b, K, r)) { res.ok = false; return res; }
        a = std::move(b);
        b = std::move(r);
    }
    int da = kdeg(a, K);
    if (da < 0) {                                 // gcd(0,0) — both zero
        res.gcd = RationalPolynomial();
        return res;
    }
    // Make monic over K: divide every coefficient by the leading one.
    auto leadInv = K.inverse(a[da]);
    if (!leadInv) { res.ok = false; return res; }
    for (auto& c : a) c = K.mul(c, *leadInv);
    res.gcd = fromCoeffs(a, targetVar);
    return res;
}

}  // namespace xolver
