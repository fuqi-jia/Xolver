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

}  // namespace nlcolver
