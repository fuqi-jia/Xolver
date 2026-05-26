#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/core/CdcacValue.h"   // RealAlg
#include "expr/types.h"
#include <optional>
#include <vector>

namespace zolver {

// ---------------------------------------------------------------------------
// TowerAlgebraicKernel — exact arithmetic in the field tower
//   Q(alpha_0, ..., alpha_{k-1}) ~= Q[A_0,...,A_{k-1}] / <m_0, ..., m_{k-1}>
// where each m_i is MONIC in A_i over the lower tower Q[A_0..A_{i-1}]
// (LAZARD.md [H1]). This is step B.1: exact +, -, *, and the exact zero-test.
// Real-root isolation over a tower ([H2]) is step B.2 (TowerRootIsolation).
//
// Representation: a TowerElement holds the REDUCED (normal-form) numerator, a
// RationalPolynomial in the extension variables with deg_{A_i} < deg_{A_i}(m_i)
// for every i. v1 is POLYNOMIAL ONLY (denominator == 1); any operation needing
// a field inverse is out of scope and must be reported Unsupported by callers.
//
// Exact zero-test = "reduced numerator is the zero polynomial". This decides
// equality in the quotient RING; when the m_i are the true minimal polynomials
// (irreducible over the lower tower at the chosen real embedding) it coincides
// with equality of the real values — the property B.2's exact root filter
// relies on. Interval arithmetic on `generators` may only WITNESS sign/order
// after an exact zero/nonzero decision; it never PROVES zero.
// ---------------------------------------------------------------------------

struct TowerContext {
    std::vector<VarId> extensionVars;             // A_0, A_1, ... (fresh ids)
    std::vector<RationalPolynomial> minimalPolys; // m_i, MONIC in extensionVars[i]
    std::vector<RealAlg> generators;              // alpha_i real embeddings (B.2 branch select)
    // Reserved by [H1]/[H7] for the closure wiring: closureId, prefixCells.
};

struct TowerElement {
    RationalPolynomial value;   // reduced numerator over the extension variables
    bool isZero() const { return value.isZero(); }
};

class TowerKernel {
public:
    explicit TowerKernel(TowerContext ctx) : ctx_(std::move(ctx)) {}

    const TowerContext& context() const { return ctx_; }
    int numGenerators() const { return static_cast<int>(ctx_.extensionVars.size()); }

    TowerElement fromRational(const mpq_class& q) const;
    TowerElement generator(int i) const;                 // alpha_i (reduced if deg 1)
    TowerElement reduce(const RationalPolynomial& p) const;  // arbitrary poly -> normal form

    TowerElement add(const TowerElement& a, const TowerElement& b) const;
    TowerElement sub(const TowerElement& a, const TowerElement& b) const;
    TowerElement mul(const TowerElement& a, const TowerElement& b) const;
    TowerElement neg(const TowerElement& a) const;

    bool isZero(const TowerElement& a) const { return a.value.isZero(); }
    bool equal(const TowerElement& a, const TowerElement& b) const;

    // Exact field inverse / division: recursive extended-Euclid modulo each
    // minimal poly. nullopt iff e == 0 OR a minimal poly turns out reducible
    // (a Euclid gcd is non-constant) — i.e. the irreducible-min-poly contract
    // is violated; callers then degrade to Unsupported/Unknown (never UNSAT).
    std::optional<TowerElement> inverse(const TowerElement& e) const;
    std::optional<TowerElement> div(const TowerElement& a, const TowerElement& b) const;

private:
    TowerContext ctx_;

    // Triangular reduction modulo <m_0,...,m_{k-1}>, highest generator first.
    RationalPolynomial reducePoly(RationalPolynomial p) const;
    // Reduce p modulo only the first `count` minimal polys (lower-tower coeffs).
    RationalPolynomial reduceUpTo(RationalPolynomial p, int count) const;
    // Exact monic reduction of p modulo a single m_i in variable A_i.
    static RationalPolynomial reduceByMonic(RationalPolynomial p, VarId Ai,
                                            const RationalPolynomial& mi);

    // Invert e in the field F_level = Q(A_0..A_{level-1}); recursion bottoms at
    // level 0 (rationals). level == numGenerators() is the full-tower inverse.
    std::optional<RationalPolynomial> invRec(RationalPolynomial e, int level) const;
    // Univariate (in v) division over the coefficient field F_coeffLevel.
    struct DivMod { RationalPolynomial quot, rem; };
    std::optional<DivMod> polyDivMod(RationalPolynomial a, RationalPolynomial b,
                                     VarId v, int coeffLevel) const;
};

}  // namespace zolver
