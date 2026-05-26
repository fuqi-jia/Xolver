#pragma once

#include "theory/arith/nra/CdcacTypes.h"
#include "theory/arith/nra/CdcacConstraint.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <vector>

namespace zolver {

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
     */
    virtual std::vector<PolyId> projectionPolys(
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
     * partial sample (prefix). Used for nullification detection (P4).
     */
    virtual bool vanishesAtPrefix(PolyId p, const SamplePoint& prefix, VarId var) = 0;

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
};

} // namespace zolver
