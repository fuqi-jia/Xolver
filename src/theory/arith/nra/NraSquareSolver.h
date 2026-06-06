#pragma once

#include "expr/types.h"   // VarId, PolyId, Relation
#include <gmpxx.h>
#include <optional>
#include <unordered_map>
#include <vector>

namespace xolver {

class PolynomialKernel;
class RationalPolynomial;

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

// Substitute variable `from` with variable `to` in p — EXACT, via pseudo-remainder
// by the monic linear divisor (from - to). Used to collapse two equal algebraic
// roots (same defining poly + sign, e.g. v11 = v12 = +sqrt(1/2)) onto a SINGLE
// generator, so every constraint reduces to one algebraic variable and validation
// stays 1-algebraic (signAtOneAlgebraic) instead of needing the ≥2-algebraic tower.
PolyId substituteVarWithVar(PolyId p, VarId from, VarId to, PolynomialKernel& kernel);

// Result of collapsing resolved square-roots: rational vars get exact values;
// algebraic vars that are the SAME number (equal squaredValue AND sign) collapse
// to one representative generator, with `aliasOf` mapping each onto its rep.
struct CollapsedRoots {
    bool feasible = true;                              // false if any c < 0
    std::unordered_map<VarId, mpq_class> rationalVars; // var -> exact rational value
    std::unordered_map<VarId, VarId> aliasOf;          // algebraic var -> generator rep
    std::vector<VarId> generators;                     // distinct generator reps
    std::unordered_map<VarId, mpq_class> genSquared;   // rep -> c (rep^2 = c)
    std::unordered_map<VarId, int> genSign;            // rep -> +/-1
};

// Group resolved roots: equal algebraic numbers (same squaredValue + sign) share a
// generator. Pure (no kernel).
CollapsedRoots collapseAlgebraicRoots(const std::vector<SquareRoot>& roots);

// Sign of a*sqrt(c) + b for c > 0, as -1 / 0 / +1. Pure exact rational arithmetic
// (compares a^2*c vs b^2 in the mixed-sign case). This is the 1-algebraic sign
// evaluation that lets the cascade validate Q(sqrt c) models WITHOUT the
// ≥2-algebraic Lazard tower.
int signOfRootExpr(const mpq_class& a, const mpq_class& b, const mpq_class& c);

// Sign of a polynomial (univariate in the single generator `genVar`, whose value is
// genSign*sqrt(c), c > 0) at that generator, as -1/0/+1. Reduces modulo
// genVar^2 = c to a*genVar + b, then signOfRootExpr with the generator's sign
// folded in. Returns nullopt iff rp mentions any variable other than genVar (the
// caller must have substituted all rational vars and collapsed aliases first).
std::optional<int> signOfPolyAtGenerator(const RationalPolynomial& rp, VarId genVar,
                                         const mpq_class& c, int genSign);

}  // namespace xolver
