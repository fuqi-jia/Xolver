#pragma once

#include "expr/types.h"   // VarId, PolyId, Relation
#include <gmpxx.h>
#include <optional>
#include <vector>

namespace xolver {

class PolynomialKernel;

// Foundation for the NRA algebraic SQUARE-CASCADE (Task #2: algebraic SAT model
// construction). The dominant residual QF_NRA gap is square-defined algebraic SAT
// (e.g. Geogebra IsoRightTriangle: v11^2 = 1/2 -> v11 = 1/sqrt2, whole model in
// Q(sqrt2)). The rational-only eq-cascade cannot construct these. This module
// detects and solves the square equalities that seed such a model.
//
// A "square equality" is a*x^2 + b = 0 that is UNIVARIATE in x and has only the
// x^2 and constant terms (no x^1) — i.e. x^2 = -b/a. Such an equality fixes x to
// +/- sqrt(-b/a), the sign chosen by an accompanying strict bound (0 < x / x < 0).
struct SquareEquality {
    VarId var;                 // x
    mpq_class squaredValue;    // c, where x^2 = c   (c = -b/a)
    size_t constraintIndex;    // index into the input equality list
};

// Outcome of resolving x^2 = c with an optional sign constraint.
struct SquareRoot {
    VarId var;
    bool feasible;             // false iff c < 0 (no real root) — the branch is UNSAT
    bool isRational;           // true iff c is a perfect rational square (x is rational)
    mpq_class rationalValue;   // valid iff isRational (the chosen +/- sqrt(c))
    mpq_class squaredValue;    // c (for the algebraic case: x is a root of x^2 - c)
    int sign;                  // +1 / -1 chosen from the bound; +1 default if unconstrained
};

// Scan `eqs` (each {poly, rel} with rel == Eq) for square equalities. Pure; never
// touches libpoly root isolation. Returns one SquareEquality per qualifying eq.
std::vector<SquareEquality> detectSquareEqualities(
    const std::vector<std::pair<PolyId, Relation>>& eqs, PolynomialKernel& kernel);

// Resolve a detected square equality to a concrete (rational or algebraic) root,
// honoring a sign hint (+1 / -1 / 0=unconstrained).
SquareRoot solveSquareRoot(const SquareEquality& sq, int signHint);

// True iff `c` (>= 0) is a perfect square of a rational; if so, sets `root` to its
// non-negative square root. c must be in lowest terms is NOT required.
bool rationalSqrt(const mpq_class& c, mpq_class& root);

}  // namespace xolver
