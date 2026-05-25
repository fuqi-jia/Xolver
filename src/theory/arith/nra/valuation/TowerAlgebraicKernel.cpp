#include "theory/arith/nra/valuation/TowerAlgebraicKernel.h"

namespace nlcolver {

// Exact monic reduction: while deg_{Ai}(p) >= deg_{Ai}(mi), cancel the leading
// A_i power by subtracting lead * A_i^(e-di) * mi. Because mi is monic in A_i
// this is true polynomial division (no spurious denominator/scale). Each step
// strictly lowers deg_{Ai}(p), so it terminates with deg_{Ai}(p) < deg_{Ai}(mi).
RationalPolynomial TowerKernel::reduceByMonic(RationalPolynomial p, VarId Ai,
                                              const RationalPolynomial& mi) {
    int di = mi.degree(Ai);
    if (di < 0) return p;   // mi independent of Ai (degenerate context); nothing to do
    while (true) {
        int e = p.degree(Ai);
        if (e < di) break;
        RationalPolynomial lead = p.leadingCoefficient(Ai);   // coeff of A_i^e (lower vars)
        RationalPolynomial shift = (e - di == 0)
            ? RationalPolynomial::fromConstant(mpq_class(1))
            : RationalPolynomial::fromVar(Ai, e - di, mpq_class(1));
        RationalPolynomial toSub = lead * shift * mi;
        p = p - toSub;
        p.normalize();
    }
    return p;
}

RationalPolynomial TowerKernel::reducePoly(RationalPolynomial p) const {
    p.normalize();
    // Highest generator first: reducing A_i may introduce lower A_j terms, but
    // never higher ones, so a single top-down pass yields the normal form.
    for (int i = static_cast<int>(ctx_.extensionVars.size()) - 1; i >= 0; --i) {
        p = reduceByMonic(std::move(p), ctx_.extensionVars[i], ctx_.minimalPolys[i]);
    }
    p.normalize();
    return p;
}

TowerElement TowerKernel::fromRational(const mpq_class& q) const {
    return TowerElement{RationalPolynomial::fromConstant(q)};
}

TowerElement TowerKernel::generator(int i) const {
    RationalPolynomial a = RationalPolynomial::fromVar(ctx_.extensionVars[i], 1, mpq_class(1));
    return TowerElement{reducePoly(std::move(a))};
}

TowerElement TowerKernel::reduce(const RationalPolynomial& p) const {
    return TowerElement{reducePoly(p)};
}

TowerElement TowerKernel::add(const TowerElement& a, const TowerElement& b) const {
    // Sum of two reduced elements is already reduced (degrees do not grow).
    RationalPolynomial s = a.value + b.value;
    s.normalize();
    return TowerElement{std::move(s)};
}

TowerElement TowerKernel::sub(const TowerElement& a, const TowerElement& b) const {
    RationalPolynomial s = a.value - b.value;
    s.normalize();
    return TowerElement{std::move(s)};
}

TowerElement TowerKernel::neg(const TowerElement& a) const {
    return TowerElement{-a.value};
}

TowerElement TowerKernel::mul(const TowerElement& a, const TowerElement& b) const {
    // Product can exceed the per-variable degree bound, so re-reduce.
    return TowerElement{reducePoly(a.value * b.value)};
}

bool TowerKernel::equal(const TowerElement& a, const TowerElement& b) const {
    RationalPolynomial d = a.value - b.value;
    d.normalize();
    return d.isZero();
}

RationalPolynomial TowerKernel::reduceUpTo(RationalPolynomial p, int count) const {
    p.normalize();
    for (int i = count - 1; i >= 0; --i)
        p = reduceByMonic(std::move(p), ctx_.extensionVars[i], ctx_.minimalPolys[i]);
    p.normalize();
    return p;
}

// Univariate long division in v, with coefficients in the field F_coeffLevel
// (a poly in A_0..A_{coeffLevel-1}). Leading-coefficient inverse via invRec.
std::optional<TowerKernel::DivMod> TowerKernel::polyDivMod(
    RationalPolynomial a, RationalPolynomial b, VarId v, int coeffLevel) const {
    if (b.isZero()) return std::nullopt;
    int db = b.degree(v);
    if (db < 0) return std::nullopt;
    auto lcbInv = invRec(b.leadingCoefficient(v), coeffLevel);
    if (!lcbInv) return std::nullopt;

    RationalPolynomial quot;            // zero
    RationalPolynomial rem = reduceUpTo(std::move(a), coeffLevel);
    int guard = 0;
    while (true) {
        rem.normalize();
        int dr = rem.degree(v);
        if (rem.isZero() || dr < db) break;
        if (++guard > 100000) return std::nullopt;
        RationalPolynomial factor = reduceUpTo(rem.leadingCoefficient(v) * (*lcbInv), coeffLevel);
        RationalPolynomial mono = (dr - db == 0)
            ? RationalPolynomial::fromConstant(mpq_class(1))
            : RationalPolynomial::fromVar(v, dr - db, mpq_class(1));
        RationalPolynomial term = factor * mono;
        quot = quot + term;
        rem = reduceUpTo(rem - reduceUpTo(term * b, coeffLevel), coeffLevel);
    }
    return DivMod{reduceUpTo(std::move(quot), coeffLevel), rem};
}

std::optional<RationalPolynomial> TowerKernel::invRec(RationalPolynomial e, int level) const {
    e = reduceUpTo(std::move(e), level);
    if (e.isZero()) return std::nullopt;
    if (level == 0) {
        if (!e.isConstant()) return std::nullopt;
        mpq_class c = e.constantValue();
        if (c == 0) return std::nullopt;
        return RationalPolynomial::fromConstant(mpq_class(1) / c);
    }
    VarId v = ctx_.extensionVars[level - 1];
    const RationalPolynomial& m = ctx_.minimalPolys[level - 1];
    int cf = level - 1;

    // Extended Euclid over F_cf: r0 = m, r1 = e; s_i tracks the cofactor of e.
    RationalPolynomial r0 = m, r1 = e;
    RationalPolynomial s0 = RationalPolynomial::fromConstant(mpq_class(0));
    RationalPolynomial s1 = RationalPolynomial::fromConstant(mpq_class(1));
    int guard = 0;
    while (!r1.isZero()) {
        if (++guard > 100000) return std::nullopt;
        auto dm = polyDivMod(r0, r1, v, cf);
        if (!dm) return std::nullopt;
        RationalPolynomial s2 = reduceUpTo(s0 - dm->quot * s1, level);
        r0 = r1; r1 = dm->rem;
        s0 = s1; s1 = std::move(s2);
    }
    if (r0.degree(v) > 0) return std::nullopt;   // gcd non-constant => m reducible (contract broken)
    auto ginv = invRec(r0, cf);                  // invert the F_cf constant gcd
    if (!ginv) return std::nullopt;
    return reduceUpTo(s0 * (*ginv), level);      // e^{-1} = cofactor(e) * gcd^{-1} (mod m)
}

std::optional<TowerElement> TowerKernel::inverse(const TowerElement& e) const {
    auto r = invRec(e.value, numGenerators());
    if (!r) return std::nullopt;
    return TowerElement{reducePoly(*r)};
}

std::optional<TowerElement> TowerKernel::div(const TowerElement& a, const TowerElement& b) const {
    auto bi = inverse(b);
    if (!bi) return std::nullopt;
    return mul(a, *bi);
}

}  // namespace nlcolver
