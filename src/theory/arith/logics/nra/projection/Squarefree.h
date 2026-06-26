#pragma once

#include "theory/arith/kernel/poly/RationalPolynomial.h"
#include "expr/types.h"

namespace xolver {

class PolynomialKernel;

// Multivariate content / primitive part / squarefree part w.r.t. an explicit
// variable v, with coefficients in Q[lower vars]. See LAZARD.md [H4]. These are
// the primitives the Lazard projection operator needs to form its primitive
// squarefree basis; the existing RationalPolynomial::content/primitivePart
// (which return 1 for multivariate coefficients) are insufficient.
//
// Results are up-to-rational-unit (monic in the largest monomial), matching the
// projection closure's intern() canonicalization. `complete == false` means an
// exact gcd/division step was unsupported (non-exact subresultant gcd); the
// caller MUST then treat the closure as incomplete (=> Unknown, never UNSAT).
struct SquarefreeResult {
    RationalPolynomial poly;
    bool complete = true;
};

// gcd over Q[lower vars] of the v-coefficients of p. Zero poly => zero content;
// any unit (constant) coefficient => content 1.
//
// `kernel` is OPTIONAL. When non-null, each pairwise gcd step goes through
// libpoly's EXACT multivariate gcd (PolynomialKernel::gcd) — robust on the
// high-degree multivariate inputs where the hand-rolled subresultant PRS
// suffers coefficient blowup. The libpoly gcd is STILL verified by exactDivide
// (a disagreement falls back / marks incomplete). When `kernel == nullptr` the
// existing hand-rolled subresultant path runs unchanged (byte-identical).
SquarefreeResult contentWrt(const RationalPolynomial& p, VarId v,
                            PolynomialKernel* kernel = nullptr);

// p / content_v(p). Constant/zero content => p (monic-normalized).
SquarefreeResult primitivePartWrt(const RationalPolynomial& p, VarId v,
                                  PolynomialKernel* kernel = nullptr);

// primitivePart_v(p) / gcd_v(pp, d pp / dv): the squarefree part w.r.t. v.
SquarefreeResult squarefreePartWrt(const RationalPolynomial& p, VarId v,
                                   PolynomialKernel* kernel = nullptr);

}  // namespace xolver
