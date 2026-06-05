#pragma once

#include "theory/arith/nra/backend/AlgebraBackend.h"

namespace xolver {

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
    VanishResult vanishesAtPrefix(PolyId p, const SamplePoint& prefix, VarId var) override;
    CompareResult compareRealAlg(const RealAlg& a, const RealAlg& b) override;
    RootSet isolateRealRootsAlgebraic(
        PolyId p, const SamplePoint& prefix, VarId mainVar) override;

    // SAFE algebraic-prefix root isolation (single algebraic coordinate) via
    // resultant Norm over Q + exact rational interval filter. Never invokes
    // libpoly's crash-prone algebraic root isolation. See AlgebraBackend.
    RootSet isolateRealRootsViaNorm(
        PolyId p, const SamplePoint& prefix, VarId mainVar, bool& supported) override;

    // Lazard tower root isolation for the MULTI algebraic-coordinate case (the
    // tower that ViaNorm punts on). See AlgebraBackend::isolateRealRootsViaTower.
    RootSet isolateRealRootsViaTower(
        PolyId p, const SamplePoint& prefix, VarId mainVar, bool& supported) override;

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

    // Refine the isolating interval of an algebraic root
    bool refineRootInterval(AlgebraicRoot& root) override;

    // --- P2a univariate algebraic helpers ---

    // Sign of univariate polynomial g at algebraic root alpha.
    // Kept public for unit testing (Test A: endpoint shortcut killer).
    Sign signUnivariateAtAlgebraic(UniPolyId g, const AlgebraicRoot& alpha);

private:
    PolynomialKernel* kernel_;
    LibPolyKernel* libKernel_ = nullptr;  // null if kernel is not LibPolyKernel

    // UniPolyId pool: stores coefficient vectors (high-to-low degree, integer coeffs)
    std::vector<std::vector<mpz_class>> uniPool_;

    // Helper: build mpq_class sample map from SamplePoint (rational values only)
    std::unordered_map<VarId, mpq_class> toRationalMap(const SamplePoint& sample) const;

    // Helper: evaluate univariate polynomial at a rational point
    mpq_class evalUniAtRational(const std::vector<mpz_class>& coeffs, const mpq_class& q) const;

    // P2d: signAt layers
    Sign signAtRational(PolyId p, const SamplePoint& sample);
    Sign signAtOneAlgebraic(PolyId p, const SamplePoint& sample);
    Sign signAtTower(PolyId p, const SamplePoint& sample);

    // Crash-guarded libpoly algebraic sign evaluation (never-crash rule). Each
    // wraps a libpoly call that can SIGSEGV on a malformed/non-squarefree defining
    // poly in the sigsetjmp recovery harness, returning Sign::Unknown on a
    // recovered crash. Isolated in their own frame so the callers' live locals
    // cannot be clobbered by longjmp (-Wclobbered). Result: -1/0/+1 sign with
    // `ok=false` => Unknown.
    //   poly::sgn(current, algebraic-and-rational assignment over `sample`).
    Sign signAtSampleGuarded(PolyId current, const SamplePoint& sample);
    //   poly::sgn(g specialized, single algebraic alpha) — the univariate case.
    Sign signUnivariateAtAlgebraicGuarded(const std::vector<mpz_class>& gCoeffs,
                                          const AlgebraicRoot& alpha);
    // Exact algebraic-number comparison via libpoly's lp_value_cmp, used as a
    // sound fallback when compareRealAlg's manual interval refinement exhausts
    // its budget (returns Unknown). Crash-guarded; firewall-gated.
    CompareResult compareRealAlgViaLibpolyGuarded(const RealAlg& a, const RealAlg& b);

    // Helper: convert UniPolyId coefficient vector back to PolyId in given variable
    PolyId univariateToPoly(const std::vector<mpz_class>& coeffs, VarId var);

    // Count real roots of univariate polynomial h in open interval (lo, hi)
    int countRealRootsInInterval(UniPolyId h, const mpq_class& lo, const mpq_class& hi);

    // Locate alpha's position among real roots of another polynomial h
    RootLocateResult locateRootInPolynomial(const AlgebraicRoot& alpha, UniPolyId h);

};

} // namespace xolver
