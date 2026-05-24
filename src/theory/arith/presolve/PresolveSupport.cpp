#include "theory/arith/presolve/Presolve.h"

namespace nlcolver {

RationalPolynomial substituteVar(const RationalPolynomial& p, VarId v,
                                 const RationalPolynomial& value) {
    RationalPolynomial result;
    for (const auto& [key, coeff] : p.terms()) {
        int ev = 0;
        MonomialKey rest;
        for (const auto& [var, exp] : key) {
            if (var == v) ev = exp;
            else rest.push_back({var, exp});
        }
        // term = coeff * (rest monomial) * value^ev
        RationalPolynomial term = RationalPolynomial::fromConstant(coeff);
        if (!rest.empty()) {
            RationalPolynomial restPoly;
            restPoly.addTerm(rest, mpq_class(1));
            term = term * restPoly;
        }
        if (ev > 0) {
            term = term * value.pow(static_cast<uint32_t>(ev));
        }
        result += term;
    }
    result.normalize();
    return result;
}

int totalDegree(const RationalPolynomial& p) {
    int maxd = 0;
    for (const auto& [key, coeff] : p.terms()) {
        (void)coeff;
        int d = 0;
        for (const auto& [var, exp] : key) { (void)var; d += exp; }
        if (d > maxd) maxd = d;
    }
    return maxd;
}

bool relationHoldsForConstant(const mpq_class& c, Relation rel) {
    switch (rel) {
        case Relation::Eq:  return c == 0;
        case Relation::Neq: return c != 0;
        case Relation::Lt:  return c < 0;
        case Relation::Leq: return c <= 0;
        case Relation::Gt:  return c > 0;
        case Relation::Geq: return c >= 0;
    }
    return false;
}

} // namespace nlcolver
