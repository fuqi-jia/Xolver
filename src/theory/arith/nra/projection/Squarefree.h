#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "expr/types.h"

namespace nlcolver {

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
SquarefreeResult contentWrt(const RationalPolynomial& p, VarId v);

// p / content_v(p). Constant/zero content => p (monic-normalized).
SquarefreeResult primitivePartWrt(const RationalPolynomial& p, VarId v);

// primitivePart_v(p) / gcd_v(pp, d pp / dv): the squarefree part w.r.t. v.
SquarefreeResult squarefreePartWrt(const RationalPolynomial& p, VarId v);

}  // namespace nlcolver
