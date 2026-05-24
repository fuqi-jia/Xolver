#pragma once

#include "expr/ir.h"
#include <gmpxx.h>
#include <optional>
#include <unordered_map>
#include <vector>

namespace nlcolver {

/**
 * ModularConsistencyChecker: CRT-based preprocessing for
 * (= (mod x N) c) patterns with constant divisors N and constant residues c.
 *
 * Runs BEFORE IntDivModLowerer (which would replace mod with linear
 * arithmetic over fresh quotient/remainder variables — at which point CRT
 * reasoning is no longer recoverable in closed form). For each integer
 * variable x with one or more mod-equality constraints:
 *
 *   1. Aggregate (modulus, residue) pairs via pairwise CRT. If pairwise
 *      gcd does not divide the residue difference, the conjunction is
 *      unsatisfiable; emit a false assertion at the original scope.
 *   2. Combine into a single (residue mod lcm) when consistent.
 *   3. If x carries inclusive integer bounds [lo, hi] (also collected
 *      from top-level assertions), enumerate candidates in range:
 *        * no candidate in range → emit false;
 *        * exactly one candidate → pin x = candidate;
 *        * otherwise leave as-is for the downstream solver.
 *
 * Soundness notes:
 *   * Only top-level assertions are inspected; mod patterns nested under
 *     boolean composites are left to the standard pipeline.
 *   * Strict bounds are tightened to inclusive using integer-tight (`>` to
 *     `>=`+1 etc.) so the enumeration is exact.
 *   * The original assertions are NOT removed — emitting `false` short-
 *     circuits the SAT side, and emitting `x = c` is consistent with every
 *     mod constraint by construction (so the surviving assertions are
 *     redundant rather than contradictory).
 */
class ModularConsistencyChecker {
public:
    explicit ModularConsistencyChecker(CoreIr& ir);

    void run();

private:
    struct ModConstraint {
        ExprId varExpr;
        mpz_class modulus;
        mpz_class residue;
        ExprId origAssertion;
        ScopeLevel level;
    };

    struct VarBounds {
        std::optional<mpz_class> lo;  // inclusive
        std::optional<mpz_class> hi;  // inclusive
        ScopeLevel level = 0;
    };

    std::optional<ModConstraint> matchModEq(ExprId assertion, ScopeLevel level);

    bool matchBound(ExprId assertion, ScopeLevel level,
                    std::unordered_map<ExprId, VarBounds>& bounds);

    static void crtCombine(const mpz_class& a1, const mpz_class& n1,
                           const mpz_class& a2, const mpz_class& n2,
                           mpz_class& a, mpz_class& n, bool& ok);

    ExprId mkFalse();
    ExprId mkIntConst(const mpz_class& v);
    ExprId mkEq(ExprId a, ExprId b);

    CoreIr& ir_;
    SortId boolSortId_;
    SortId intSortId_;
};

} // namespace nlcolver
