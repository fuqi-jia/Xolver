#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <vector>

namespace nlcolver {

/**
 * Abstract algebra backend for CDCAC.
 *
 * All exact polynomial / root / sign operations go through this interface.
 * libpoly must only appear inside LibpolyBackend, not in CdcacCore or
 * CdcacSolver main logic.
 */
class AlgebraBackend {
public:
    virtual ~AlgebraBackend() = default;

    /**
     * Root isolation for a univariate polynomial (already specialized).
     * Returns ordered real roots.
     */
    virtual RootSet isolateRealRoots(UniPolyId p) = 0;

    /**
     * Sign of a multivariate polynomial at a sample point.
     * SamplePoint may contain algebraic values (P1+).
     *
     * Special rule for P1: if the polynomial being evaluated is the same
     * defining polynomial as an algebraic root in the sample (same UniPolyId
     * and rootIndex), this must return Sign::Zero directly without relying
     * on interval refinement.
     */
    virtual Sign signAt(PolyId p, const SamplePoint& sample) = 0;

    /**
     * Specialize a multivariate polynomial to univariate by substituting
     * the prefix sample for all variables except mainVar.
     */
    virtual UniPolyId specializeToUnivariate(
        PolyId p,
        const SamplePoint& prefix,
        VarId mainVar
    ) = 0;

    /**
     * Projection: eliminate eliminateVar from polys, return new polynomial set.
     * P2b: returns status + polynomials. UnsupportedVarOrder / BackendFailure
     * must be treated as "no projection available" (safe silent degradation).
     */
    virtual ProjectionResult projectionPolys(
        const std::vector<PolyId>& polys,
        VarId eliminateVar,
        ProjectionMode mode
    ) = 0;

    /**
     * Self-check: validate that root isolation is correct.
     * (Sturm count, disjoint intervals, endpoints not roots, etc.)
     */
    virtual bool validateRootIsolation(UniPolyId p, const RootSet& roots) = 0;

    /**
     * Check whether a polynomial vanishes (is identically zero) under a
     * partial sample (prefix). Used for nullification detection (P4/V2-7).
     *
     * Rational prefix: returns Vanishes or NonVanishes.
     * Algebraic prefix: returns Unknown (not supported in V2-7).
     */
    virtual VanishResult vanishesAtPrefix(PolyId p, const SamplePoint& prefix, VarId var) = 0;

    /**
     * Compare two real algebraic numbers.
     * Uses algebraic proofs (gcd, same defining poly) and certified refinement.
     * Returns Unknown only on resource exhaustion or unsupported cases.
     */
    virtual CompareResult compareRealAlg(const RealAlg& a, const RealAlg& b) = 0;

    /**
     * Root isolation with algebraic prefix assignment (P4).
     * Substitutes prefix values (which may include algebraic numbers) into p,
     * then isolates real roots of the resulting univariate polynomial in mainVar.
     *
     * Returns empty RootSet if unsupported or fails.
     */
    virtual RootSet isolateRealRootsAlgebraic(
        PolyId p,
        const SamplePoint& prefix,
        VarId mainVar) {
        (void)p; (void)prefix; (void)mainVar;
        return RootSet{};
    }

    /**
     * SAFE algebraic-prefix root isolation (single algebraic coordinate) via
     * resultant Norm + exact rational interval filter. Does NOT use the
     * crash-prone libpoly algebraic root isolation. `supported` is set true
     * only when a certified isolation completed (0 roots is then a valid
     * answer); false on the tower / unsupported / degenerate cases (caller
     * must treat as Unknown, never UNSAT).
     */
    virtual RootSet isolateRealRootsViaNorm(
        PolyId p,
        const SamplePoint& prefix,
        VarId mainVar,
        bool& supported) {
        (void)p; (void)prefix; (void)mainVar;
        supported = false;
        return RootSet{};
    }

    /**
     * Lazard tower root isolation (MULTI algebraic coordinate / genuine tower) —
     * the case isolateRealRootsViaNorm punts on. Builds the field tower from the
     * algebraic prefix coordinates (each coord's defining poly as a monic
     * minimal poly), computes the rational Norm, isolates its roots over Q, and
     * keeps exactly those that are roots of p at the real embedding via the exact
     * three-state membership oracle (sound on a reducible tower). `supported` is
     * true only when EVERY candidate was decided Keep/Drop; any Unknown / Norm
     * degeneracy => supported=false (caller treats as Unknown, never UNSAT).
     * Default: unsupported (only LibpolyBackend implements it).
     */
    virtual RootSet isolateRealRootsViaTower(
        PolyId p,
        const SamplePoint& prefix,
        VarId mainVar,
        bool& supported) {
        (void)p; (void)prefix; (void)mainVar;
        supported = false;
        return RootSet{};
    }

    /**
     * Refine the isolating interval of an algebraic root.
     * Returns true if refinement succeeded (interval was narrowed).
     * Returns false if refinement failed or the root is rational.
     */
    virtual bool refineRootInterval(AlgebraicRoot& root) {
        (void)root;
        return false;
    }
};

} // namespace nlcolver
