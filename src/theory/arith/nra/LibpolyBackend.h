#pragma once

#include "theory/arith/nra/AlgebraBackend.h"

namespace nlcolver {

class PolynomialKernel;
class LibPolyKernel;

/**
 * AlgebraBackend implementation backed by libpoly.
 *
 * All libpoly calls are encapsulated here. If libpoly is unavailable
 * or returns invalid results, this backend returns Unknown / false / empty.
 *
 * UniPolyId in this backend indexes a pool of internally-managed univariate
 * polynomial representations (coefficient vectors), which are converted to
 * libpoly UPolynomial on demand.
 */
class LibpolyBackend final : public AlgebraBackend {
public:
    explicit LibpolyBackend(PolynomialKernel* kernel);

    RootSet isolateRealRoots(UniPolyId p) override;
    Sign signAt(PolyId p, const SamplePoint& sample) override;
    UniPolyId specializeToUnivariate(PolyId p, const SamplePoint& prefix, VarId mainVar) override;
    ProjectionResult projectionPolys(const std::vector<PolyId>& polys, VarId eliminateVar, ProjectionMode mode) override;
    bool validateRootIsolation(UniPolyId p, const RootSet& roots) override;
    bool vanishesAtPrefix(PolyId p, const SamplePoint& prefix, VarId var) override;
    CompareResult compareRealAlg(const RealAlg& a, const RealAlg& b) override;
    RootSet isolateRealRootsAlgebraic(
        PolyId p, const SamplePoint& prefix, VarId mainVar) override;

    // --- V2-1: univariate polynomial pool access (public for engines) ---

    UniPolyId allocUni(std::vector<mpz_class> coeffs);
    const std::vector<mpz_class>& getUni(UniPolyId id) const;

    // GCD of two univariate polynomials (returns 0 if both are zero)
    UniPolyId gcdUni(UniPolyId a, UniPolyId b);

    // True if univariate polynomial is a non-zero constant
    bool isConstantUni(UniPolyId p) const;

    // V2-1: exact division of univariate polynomials
    // Returns NullUniPolyId if b does not divide a exactly.
    UniPolyId exactDivideUni(UniPolyId a, UniPolyId b);

private:
    PolynomialKernel* kernel_;
    LibPolyKernel* libKernel_ = nullptr;  // null if kernel is not LibPolyKernel

    // UniPolyId pool: stores coefficient vectors (high-to-low degree, integer coeffs)
    std::vector<std::vector<mpz_class>> uniPool_;

    // Helper: build mpq_class sample map from SamplePoint (rational values only)
    std::unordered_map<VarId, mpq_class> toRationalMap(const SamplePoint& sample) const;

    // Helper: evaluate univariate polynomial at a rational point
    mpq_class evalUniAtRational(const std::vector<mpz_class>& coeffs, const mpq_class& q) const;

    // --- P2a univariate algebraic helpers ---

    // Check if algebraic root alpha is also a root of univariate polynomial g
    bool rootBelongsTo(const AlgebraicRoot& alpha, UniPolyId g);

    // Sign of univariate polynomial g at algebraic root alpha
    Sign signUnivariateAtAlgebraic(UniPolyId g, const AlgebraicRoot& alpha);

    // P2d: signAt layers
    Sign signAtRational(PolyId p, const SamplePoint& sample);
    Sign signAtOneAlgebraic(PolyId p, const SamplePoint& sample);
    Sign signAtTower(PolyId p, const SamplePoint& sample);

    // Helper: convert UniPolyId coefficient vector back to PolyId in given variable
    PolyId univariateToPoly(const std::vector<mpz_class>& coeffs, VarId var);

    // Refine isolating interval of an algebraic root (bisection)
    bool refineRootInterval(AlgebraicRoot& alpha);

    // Count real roots of univariate polynomial h in open interval (lo, hi)
    int countRealRootsInInterval(UniPolyId h, const mpq_class& lo, const mpq_class& hi);

    // Locate alpha's position among real roots of another polynomial h
    RootLocateResult locateRootInPolynomial(const AlgebraicRoot& alpha, UniPolyId h);

};

} // namespace nlcolver
