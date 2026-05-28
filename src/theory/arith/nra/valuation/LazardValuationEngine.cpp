#include "theory/arith/nra/valuation/LazardValuationEngine.h"

namespace xolver {

namespace {

// Exact monic reduction of p modulo m (monic in Aj): substitute Aj = alpha_j in
// the quotient ring. Same operation as TowerKernel::reduceByMonic.
RationalPolynomial reduceByMonic(RationalPolynomial p, VarId Aj, const RationalPolynomial& m) {
    int dm = m.degree(Aj);
    if (dm < 0) return p;
    while (true) {
        int e = p.degree(Aj);
        if (e < dm) break;
        RationalPolynomial lead = p.leadingCoefficient(Aj);
        RationalPolynomial shift = (e - dm == 0)
            ? RationalPolynomial::fromConstant(mpq_class(1))
            : RationalPolynomial::fromVar(Aj, e - dm, mpq_class(1));
        p = p - lead * shift * m;
        p.normalize();
    }
    return p;
}

// Reduce q modulo m_j with derivative-order recovery: the residual is the
// lowest ∂^r/∂Aj^r q that does not vanish modulo m_j.
struct OneVar { bool ok; int multiplicity; RationalPolynomial result; };
OneVar evalOneVar(const RationalPolynomial& q, VarId Aj, const RationalPolynomial& m) {
    int maxr = q.degree(Aj);
    if (maxr < 0) {                       // q independent of Aj: substitution is identity
        return {true, 0, q};
    }
    RationalPolynomial d = q;
    for (int r = 0; r <= maxr; ++r) {
        RationalPolynomial s = reduceByMonic(d, Aj, m);
        s.normalize();
        if (!s.isZero()) return {true, r, s};
        d = d.derivative(Aj);
        d.normalize();
        if (d.isZero()) break;
    }
    return {false, 0, RationalPolynomial()};   // all derivatives vanish mod m_j
}

}  // namespace

LazardValuationResult lazardEvaluateToUnivariate(const RationalPolynomial& p,
                                                 VarId targetVar,
                                                 const TowerContext& ctx) {
    (void)targetVar;   // targetVar is never reduced; it simply survives as the lift variable
    LazardValuationResult out;
    RationalPolynomial q = p;
    q.normalize();

    // Process the prefix coordinates in variable order (A_0, A_1, ...).
    for (size_t j = 0; j < ctx.extensionVars.size(); ++j) {
        VarId Aj = ctx.extensionVars[j];
        OneVar ov = evalOneVar(q, Aj, ctx.minimalPolys[j]);
        if (!ov.ok) { out.status = ValuationStatus::AllDerivativesZero; return out; }
        out.trace.push_back({Aj, ov.multiplicity});
        q = std::move(ov.result);
        q.normalize();
    }

    out.univariate = std::move(q);
    out.status = ValuationStatus::Complete;
    return out;
}

}  // namespace xolver
