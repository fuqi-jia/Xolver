#include "theory/arith/nra/preprocess/SubresultantEngine.h"

namespace nlcolver {

SubresultantEngine::Result SubresultantEngine::run(
    const RationalPolynomial& p,
    const RationalPolynomial& q,
    VarId var) {

    Result result;

    if (p.isZero()) {
        result.gcdCandidate = q;
        return result;
    }
    if (q.isZero()) {
        result.gcdCandidate = p;
        return result;
    }

    int degP = p.degree(var);
    int degQ = q.degree(var);

    // Ensure deg(p) >= deg(q)
    RationalPolynomial r0 = (degP >= degQ) ? p : q;
    RationalPolynomial r1 = (degP >= degQ) ? q : p;

    result.sequence.push_back({r0, r0.degree(var)});
    result.sequence.push_back({r1, r1.degree(var)});

    int iteration = 0;
    while (!r1.isZero()) {
        RationalPolynomial rem = r0.pseudoRemainder(var, r1);
        int degRem = rem.degree(var);

        // Check for parametric degree drop
        int expectedDeg = r1.degree(var) - 1;
        if (degRem < expectedDeg && degRem >= 0) {
            result.hasParametricDegreeDrop = true;
        }

        r0 = r1;
        r1 = rem;

        result.sequence.push_back({r0, r0.degree(var)});

        ++iteration;
        if (iteration > 100) {
            // Safety limit
            result.gcdCandidate = RationalPolynomial();
            return result;
        }
    }

    result.gcdCandidate = r0;
    return result;
}

} // namespace nlcolver
