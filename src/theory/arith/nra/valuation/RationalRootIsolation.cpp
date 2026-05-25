#include "theory/arith/nra/valuation/RationalRootIsolation.h"
#include <algorithm>

namespace nlcolver {

namespace {

using UniQ = std::vector<mpq_class>;   // coeff[i] = coefficient of x^i

int udeg(const UniQ& a) {
    for (int i = static_cast<int>(a.size()) - 1; i >= 0; --i)
        if (a[i] != 0) return i;
    return -1;
}
void utrim(UniQ& a) {
    int d = udeg(a);
    a.resize(d < 0 ? 0 : d + 1);
}
mpq_class ueval(const UniQ& a, const mpq_class& x) {
    mpq_class r = 0;
    for (int i = static_cast<int>(a.size()) - 1; i >= 0; --i) r = r * x + a[i];
    return r;
}
UniQ uderiv(const UniQ& a) {
    UniQ d;
    for (int i = 1; i < static_cast<int>(a.size()); ++i) d.push_back(a[i] * i);
    utrim(d);
    return d;
}
// remainder of a mod b over Q (b != 0)
UniQ urem(UniQ a, const UniQ& b) {
    int db = udeg(b);
    while (true) {
        int da = udeg(a);
        if (da < db) break;
        mpq_class f = a[da] / b[db];
        for (int i = 0; i <= db; ++i) a[da - db + i] -= f * b[i];
        a[da] = 0;             // guard against rounding (exact, but be safe)
        utrim(a);
        if (a.empty()) break;
    }
    utrim(a);
    return a;
}
UniQ ugcd(UniQ a, UniQ b) {
    while (udeg(b) >= 0) { UniQ r = urem(a, b); a = std::move(b); b = std::move(r); }
    if (udeg(a) >= 0) {                          // make monic
        mpq_class lead = a[udeg(a)];
        for (auto& c : a) c /= lead;
    }
    return a;
}
// a / g  (exact, g divides a)
UniQ udiv(UniQ a, const UniQ& g) {
    int dg = udeg(g);
    UniQ q(std::max(0, udeg(a) - dg + 1), mpq_class(0));
    while (true) {
        int da = udeg(a);
        if (da < dg) break;
        mpq_class f = a[da] / g[dg];
        q[da - dg] = f;
        for (int i = 0; i <= dg; ++i) a[da - dg + i] -= f * g[i];
        a[da] = 0; utrim(a);
        if (a.empty()) break;
    }
    return q;
}

// Sturm sequence of the squarefree p: s0=p, s1=p', s_{k+1} = -rem(s_{k-1}, s_k).
std::vector<UniQ> sturmChain(const UniQ& sf) {
    std::vector<UniQ> s;
    s.push_back(sf);
    UniQ d = uderiv(sf);
    if (udeg(d) < 0) return s;
    s.push_back(d);
    while (udeg(s.back()) > 0) {
        UniQ r = urem(s[s.size() - 2], s.back());
        for (auto& c : r) c = -c;
        if (udeg(r) < 0) break;
        s.push_back(std::move(r));
    }
    return s;
}
int signVariations(const std::vector<UniQ>& chain, const mpq_class& x) {
    int v = 0, prev = 0;
    for (const auto& p : chain) {
        mpq_class val = ueval(p, x);
        int s = (val > 0) ? 1 : (val < 0 ? -1 : 0);
        if (s == 0) continue;
        if (prev != 0 && s != prev) ++v;
        prev = s;
    }
    return v;
}

}  // namespace

RationalRootResult isolateRationalRoots(const RationalPolynomial& p, VarId x) {
    RationalRootResult out;

    // Extract univariate coefficients; fail if any coefficient is non-constant
    // (p depends on another variable) or p is zero/constant.
    RationalPolynomial pn = p; pn.normalize();
    if (pn.isZero() || pn.isConstant()) return out;     // no isolated roots
    for (VarId v : pn.variables()) if (v != x) { out.ok = false; return out; }

    int d = pn.degree(x);
    auto coeffs = pn.coefficients(x);                   // each a constant poly
    UniQ a(d + 1, mpq_class(0));
    for (int i = 0; i <= d && i < static_cast<int>(coeffs.size()); ++i) {
        RationalPolynomial c = coeffs[i]; c.normalize();
        a[i] = c.isZero() ? mpq_class(0) : c.constantValue();
    }
    utrim(a);
    if (udeg(a) < 1) return out;

    // Squarefree part = a / gcd(a, a').
    UniQ g = ugcd(a, uderiv(a));
    UniQ sf = (udeg(g) >= 1) ? udiv(a, g) : a;
    utrim(sf);
    if (udeg(sf) < 1) return out;

    auto chain = sturmChain(sf);

    // Cauchy root bound: B = 1 + max_i |a_i / a_n|.
    int dn = udeg(sf);
    mpq_class B = 0;
    for (int i = 0; i < dn; ++i) { mpq_class r = abs(sf[i] / sf[dn]); if (r > B) B = r; }
    B += 1;
    // Ensure endpoints of the global interval are not roots (Cauchy bound is
    // strict, but be safe) by nudging outward.
    mpq_class lo0 = -B - 1, hi0 = B + 1;

    // Recursive isolation on half-open (lo, hi] via Sturm counts. With half-open
    // intervals a root at a split point `mid` is counted in the LEFT child
    // (lo, mid] and excluded from the right (mid, hi], so no special-casing and
    // no double-counting is needed.
    struct Frame { mpq_class lo, hi; int vlo, vhi; };
    std::vector<Frame> stack;
    stack.push_back({lo0, hi0, signVariations(chain, lo0), signVariations(chain, hi0)});

    int guard = 0;
    while (!stack.empty()) {
        if (++guard > 2000000) { out.ok = false; return out; }
        Frame f = stack.back(); stack.pop_back();
        int cnt = f.vlo - f.vhi;                 // roots in (lo, hi]
        if (cnt <= 0) continue;
        if (cnt == 1) {
            out.roots.push_back({f.lo, f.hi});   // one root strictly inside (endpoints non-roots)
            continue;
        }
        // Choose a split point that is NOT a root, so every reported interval
        // keeps non-root endpoints (a clean sign-change bracket). Finitely many
        // roots => some interior rational works.
        mpq_class mid = (f.lo + f.hi) / 2;
        int tries = 0;
        while (ueval(sf, mid) == 0 && tries < 16) {
            mid = f.lo + (f.hi - f.lo) * mpq_class(3 + tries, 8 + 2 * tries);
            ++tries;
        }
        if (ueval(sf, mid) == 0) { out.ok = false; return out; }   // unreachable in practice
        int vmid = signVariations(chain, mid);
        // push right then left so results come out ascending
        stack.push_back({mid, f.hi, vmid, f.vhi});
        stack.push_back({f.lo, mid, f.vlo, vmid});
    }

    std::sort(out.roots.begin(), out.roots.end(),
              [](const RealRootInterval& A, const RealRootInterval& Bv) {
                  if (A.lo != Bv.lo) return A.lo < Bv.lo;
                  return A.hi < Bv.hi;
              });
    return out;
}

}  // namespace nlcolver
