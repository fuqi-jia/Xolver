#include "theory/arith/nra/NraSquareSolver.h"

#include "theory/arith/poly/PolynomialKernel.h"

namespace xolver {

bool rationalSqrt(const mpq_class& c, mpq_class& root) {
    if (sgn(c) < 0) return false;
    mpz_class num = c.get_num();
    mpz_class den = c.get_den();   // > 0 in canonical form
    mpz_class sn, sd;
    mpz_sqrt(sn.get_mpz_t(), num.get_mpz_t());   // floor sqrt
    mpz_sqrt(sd.get_mpz_t(), den.get_mpz_t());
    if (sn * sn != num) return false;
    if (sd * sd != den) return false;
    root = mpq_class(sn, sd);
    root.canonicalize();
    return true;
}

std::vector<SquareEquality> detectSquareEqualities(
    const std::vector<std::pair<PolyId, Relation>>& eqs, PolynomialKernel& kernel) {
    std::vector<SquareEquality> out;
    for (size_t i = 0; i < eqs.size(); ++i) {
        if (eqs[i].second != Relation::Eq) continue;
        const PolyId p = eqs[i].first;
        const std::vector<std::string> vars = kernel.variables(p);
        if (vars.size() != 1) continue;                 // must be univariate in x
        auto co = kernel.getIntegerCoefficients(p, vars[0]);  // high -> low degree
        if (!co || co->size() != 3) continue;           // not exactly degree 2
        if ((*co)[1] != 0) continue;                    // an x^1 term -> not a pure square eq
        const mpz_class& A = (*co)[0];                  // x^2 coefficient
        const mpz_class& B0 = (*co)[2];                 // constant term
        if (A == 0) continue;
        mpq_class c(-B0, A);                             // x^2 = -B0 / A
        c.canonicalize();
        SquareEquality sq;
        sq.var = kernel.getOrCreateVar(vars[0]);
        sq.squaredValue = c;
        sq.constraintIndex = i;
        out.push_back(std::move(sq));
    }
    return out;
}

SquareRoot solveSquareRoot(const SquareEquality& sq, int signHint) {
    SquareRoot r;
    r.var = sq.var;
    r.squaredValue = sq.squaredValue;
    r.sign = (signHint < 0) ? -1 : +1;
    r.isRational = false;
    r.rationalValue = 0;
    r.feasible = (sgn(sq.squaredValue) >= 0);          // c < 0 => no real root
    if (!r.feasible) return r;
    mpq_class root;
    if (rationalSqrt(sq.squaredValue, root)) {
        r.isRational = true;
        r.rationalValue = mpq_class(r.sign) * root;
    }
    return r;
}

}  // namespace xolver
