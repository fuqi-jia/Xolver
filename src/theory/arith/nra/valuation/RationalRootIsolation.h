#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "expr/types.h"
#include <gmpxx.h>
#include <vector>

namespace nlcolver {

// Exact real-root isolation of a UNIVARIATE rational polynomial via Sturm
// sequences (self-contained exact ℚ arithmetic; no libpoly). Used by the Lazard
// tower root isolation ([H2]) to turn the Norm into candidate real roots.
//
// One entry per DISTINCT real root (operates on the squarefree part). A
// rational root r is reported as the degenerate interval [r, r]; an irrational
// root as an open interval (lo, hi) with lo < hi and no other root inside and
// neither endpoint a root.
struct RealRootInterval {
    mpq_class lo, hi;
    bool isPoint() const { return lo == hi; }   // exact rational root
};

struct RationalRootResult {
    std::vector<RealRootInterval> roots;   // ascending
    bool ok = true;                        // false iff p is not univariate in x
};

RationalRootResult isolateRationalRoots(const RationalPolynomial& p, VarId x);

}  // namespace nlcolver
