#pragma once

#include "expr/types.h"
#include "expr/ir.h"
#include <vector>
#include <memory>
#include <optional>
#include <unordered_map>
#include <gmpxx.h>

namespace xolver {

class RationalPolynomial;   // S2 (P6): cache key for toPrimitiveInteger memoization

/**
 * Abstract interface for a polynomial kernel.
 *
 * Owns a pool of polynomials indexed by PolyId.  All operations are
 * immutable: add/mul/pow return new PolyIds.
 *
 * This interface abstracts over the actual implementation (libpoly,
 * native GMP, etc.) so that upper layers (CAD, Simplex, NLSAT) do not
 * depend on a particular back-end.
 */
class PolynomialKernel {
public:
    virtual ~PolynomialKernel() = default;

    // ------------------------------------------------------------------
    // Variable registry (VarId is the canonical variable identity)
    // ------------------------------------------------------------------
    virtual VarId getOrCreateVar(std::string_view name) = 0;
    virtual std::optional<VarId> findVar(std::string_view name) const = 0;
    virtual std::string_view varName(VarId v) const = 0;
    virtual bool isValidVar(VarId v) const = 0;

    // ------------------------------------------------------------------
    // Factory / constants
    // ------------------------------------------------------------------
    virtual PolyId mkZero() = 0;
    virtual PolyId mkOne()  = 0;
    virtual PolyId mkConst(const mpq_class& c) = 0;
    virtual PolyId mkVar(VarId v) = 0;

    // ------------------------------------------------------------------
    // Core operations
    // ------------------------------------------------------------------
    virtual PolyId add(PolyId a, PolyId b) = 0;
    virtual PolyId sub(PolyId a, PolyId b) = 0;
    virtual PolyId neg(PolyId a) = 0;
    virtual PolyId mul(PolyId a, PolyId b) = 0;
    virtual PolyId pow(PolyId a, uint32_t k) = 0;

    // ------------------------------------------------------------------
    // Queries
    // ------------------------------------------------------------------
    virtual bool isZero(PolyId a) const = 0;
    virtual bool isConstant(PolyId a) const = 0;
    virtual mpq_class toConstant(PolyId a) const = 0; // UB if !isConstant
    virtual std::vector<std::string> variables(PolyId a) const = 0;

    // ------------------------------------------------------------------
    // Comparison (exact, for total-degree ordering etc.)
    // ------------------------------------------------------------------
    virtual bool eq(PolyId a, PolyId b) const = 0;

    // ------------------------------------------------------------------
    // Square-free factorization (for CAC characterization reduction).
    // ------------------------------------------------------------------
    // Decompose `a` into its square-free factors (non-constant). The product of
    // the factors has the SAME real-root set as `a` (multiplicity collapsed), so
    // replacing `a` by its factors in a sign-invariance/root computation is
    // ROOT-PRESERVING — sound. Default (stub / no factorizer): return {a}
    // unchanged (a valid, conservative no-op). libpoly overrides with
    // poly::square_free_factors.
    virtual std::vector<PolyId> squareFreeFactors(PolyId a) { return {a}; }

    // ------------------------------------------------------------------
    // Evaluation (for CAlC / sample checking)
    // ------------------------------------------------------------------
    virtual int sgn(PolyId a, const std::unordered_map<std::string, mpq_class>& sample) const = 0;

    // VarId-based variant for CDCAC internal use.
    virtual int sgnVarId(PolyId a, const std::unordered_map<VarId, mpq_class>& sample) const {
        std::unordered_map<std::string, mpq_class> stringSample;
        stringSample.reserve(sample.size());
        for (const auto& [vid, val] : sample) {
            stringSample[std::string(varName(vid))] = val;
        }
        return sgn(a, stringSample);
    }

    // ------------------------------------------------------------------
    // Integer evaluation (for NIA exact validation)
    // ------------------------------------------------------------------
    // Evaluate polynomial at integer assignment (exact integer arithmetic).
    // Returns nullopt if evaluation is unsupported (e.g. stub backend).
    virtual std::optional<mpz_class> evalInteger(
        PolyId a,
        const std::unordered_map<std::string, mpz_class>& sample) const = 0;

    // VarId-based variant for CDCAC internal use.
    virtual std::optional<mpz_class> evalIntegerVarId(
        PolyId a,
        const std::unordered_map<VarId, mpz_class>& sample) const {
        std::unordered_map<std::string, mpz_class> stringSample;
        stringSample.reserve(sample.size());
        for (const auto& [vid, val] : sample) {
            stringSample[std::string(varName(vid))] = val;
        }
        return evalInteger(a, stringSample);
    }

    // ------------------------------------------------------------------
    // Univariate analysis (for NIA integer root solving)
    // ------------------------------------------------------------------
    // Exact degree of polynomial with respect to a given variable.
    // Returns nullopt if not univariate in x or unsupported.
    virtual std::optional<int> degree(PolyId a, std::string_view var) const = 0;

    // For univariate polynomials only. Returns coefficients from highest degree to constant.
    // Returns nullopt if not univariate, unsupported, or coefficients unavailable.
    virtual std::optional<std::vector<mpz_class>>
    getIntegerCoefficients(PolyId a, std::string_view var) const = 0;

    // ------------------------------------------------------------------
    // Pseudo-remainder (for tower reduction in CDCAC)
    // ------------------------------------------------------------------
    struct PseudoRemainderResult {
        PolyId remainder = NullPoly;
        PolyId scaleFactor = NullPoly;  // lc(divisor)^k as a polynomial
        int exponent = 0;               // k = max(0, deg(dividend) - deg(divisor) + 1)
        bool ok() const { return remainder != NullPoly; }
    };

    // Compute the pseudo-remainder of p divided by divisor.
    // Returns nullopt if unsupported by the backend.
    virtual std::optional<PolyId> pseudoRemainder(PolyId p, PolyId divisor) {
        (void)p; (void)divisor;
        return std::nullopt;
    }

    // Compute pseudo-remainder and the scale factor polynomial.
    // VarId is the variable with respect to which pseudo-remainder is computed.
    // Even if divisor.mainVar is implied, passing it explicitly prevents bugs
    // in tower/context usage.
    virtual PseudoRemainderResult pseudoRemainderWithScale(PolyId dividend, PolyId divisor, VarId mainVar) {
        auto remOpt = pseudoRemainder(dividend, divisor);
        if (!remOpt) {
            return {NullPoly, NullPoly, 0};
        }

        auto degDividend = degree(dividend, varName(mainVar));
        auto degDivisor  = degree(divisor, varName(mainVar));

        if (!degDivisor) {
            return {NullPoly, NullPoly, 0};
        }

        if (!degDividend) {
            // Cannot determine dividend degree w.r.t. mainVar.
            // This happens when mainVar is not the main variable of dividend.
            // In tower reduction, prem may still succeed if variables match.
            // Conservative: no scale factor tracking.
            return {*remOpt, NullPoly, 0};
        }

        int k = *degDividend - *degDivisor + 1;
        if (k <= 0) {
            return {*remOpt, NullPoly, 0};
        }

        auto lcOpt = leadingCoefficient(divisor);
        if (!lcOpt) {
            return {*remOpt, NullPoly, 0};
        }

        PolyId scaleFactor = mkOne();
        for (int i = 0; i < k; ++i) {
            scaleFactor = mul(scaleFactor, *lcOpt);
        }

        return {*remOpt, scaleFactor, k};
    }

    // Leading coefficient of p with respect to its main variable.
    // Returns nullopt if unsupported.
    virtual std::optional<PolyId> leadingCoefficient(PolyId p) {
        (void)p;
        return std::nullopt;
    }

    // ------------------------------------------------------------------
    // Symbolic-modulus residue extraction (Track C1)
    // ------------------------------------------------------------------
    //
    // Compute the polynomial residue of `poly` modulo a SYMBOLIC `modulus`,
    // i.e. the canonical r such that poly = q * modulus + r with
    // deg_var(r) < deg_var(modulus) for some variable `var` that the
    // modulus is monic in.
    //
    // INTENDED USE — the modInvStep family from sqrtmodinv-hoenicke:
    //
    //     (assert (= (* denom inv2) (- 1 (* k k s s))))     -- denom*inv2 = 1 - k^2*s^2
    //     (assert (not (= 1 (mod (* denom inv2) (* s s))))) -- but its mod s^2 != 1
    //
    // Then extractSymbolicResidue(1 - k^2*s^2, s^2) returns 1 (since
    // -k^2*s^2 = (-k^2) * s^2 is divisible by s^2). The reasoner can then
    // close the contradiction: (mod (denom*inv2) s^2) = 1, contradicting the
    // assertion that it's != 1.
    //
    // PHASE 1 SCOPE (sound but conservative): only handles MONIC,
    // SINGLE-VARIABLE modulus polynomials. That covers s, s^2, s^3, ... as
    // generators — the modInvStep* shape — but rules out modulus s*t, s+1,
    // etc. Non-monic or multi-variable modulus returns nullopt and the
    // caller falls through to other reasoners (no soundness risk).
    //
    // SOUNDNESS: returns r such that poly ≡ r (mod modulus) holds in Z
    // under ANY non-zero integer assignment to the modulus variable.
    // Validated externally against z3 on s ∈ {2..7}.
    virtual std::optional<PolyId> extractSymbolicResidue(PolyId poly, PolyId modulus) {
        (void)poly; (void)modulus;
        return std::nullopt;
    }

    // ------------------------------------------------------------------
    // Principal subresultant coefficient (PSC) chain (for CAD projection)
    // ------------------------------------------------------------------
    // Principal subresultant coefficient chain of a and b with respect to
    // variable v. The returned chain is index-aligned with the determinant
    // reference principalSubresultantCoefficients(...).out.psc: entry j is the
    // j-th principal subresultant coefficient (psc_0 = resultant), for
    // j = 0 .. min(deg_v a, deg_v b) - 1.
    //
    // SOUNDNESS: the implementation MUST eliminate exactly v (not whichever
    // variable happens to be the libpoly main variable). Degenerate inputs
    // (deg_v(a) < 1 or deg_v(b) < 1) return an empty chain, matching the
    // determinant reference's early return. Base default returns {} (unsupported).
    virtual std::vector<PolyId> pscChain(PolyId a, PolyId b, VarId v) {
        (void)a; (void)b; (void)v;
        return {};
    }

    // ------------------------------------------------------------------
    // Greatest common divisor (for CAD projection content/squarefree)
    // ------------------------------------------------------------------
    // Exact multivariate, content-aware GCD of a and b (libpoly's
    // lp_polynomial_gcd: a single GCD over the recursive representation; NO
    // explicit main variable is required, it is the full multivariate gcd).
    //
    // SOUNDNESS: the result is exact (libpoly integer ring). The Lazard
    // squarefree/content path that consumes this STILL verifies the gcd by
    // exactDivide before using it, so an off-by-a-unit / unverifiable result
    // is downgraded to an incomplete closure (=> Unknown, never UNSAT).
    //
    // Base default returns NullPoly (unsupported) so non-libpoly builds fall
    // back to the existing hand-rolled subresultant gcd path.
    virtual PolyId gcd(PolyId a, PolyId b) {
        (void)a; (void)b;
        return NullPoly;
    }

    // Substitute a rational value for a variable, returning a new polynomial.
    // Returns nullopt if unsupported or the decomposition fails.
    virtual std::optional<PolyId> substituteRational(PolyId p, VarId v, const mpq_class& value) {
        (void)p; (void)v; (void)value;
        return std::nullopt;
    }

    // ------------------------------------------------------------------
    // Multivariate term decomposition (for GCD, interval evaluation, CAD)
    // ------------------------------------------------------------------
    struct MonomialTerm {
        mpz_class coefficient;                        // exact integer coefficient
        std::vector<std::pair<VarId, int>> powers;    // [(varId, exp), ...]; empty = constant term
    };

    // Return all monomial terms, INCLUDING the constant term as powers.empty().
    // For a constant polynomial c, return { MonomialTerm{c, {}} }.
    // Return nullopt only if decomposition fails, coefficients are not exact integers,
    // or backend unsupported. Base default returns nullopt.
    virtual std::optional<std::vector<MonomialTerm>> terms(PolyId) const {
        return std::nullopt;
    }

    // ------------------------------------------------------------------
    // Debugging
    // ------------------------------------------------------------------
    virtual std::string toString(PolyId a) const = 0;

    // ------------------------------------------------------------------
    // S2 (P6) — optional driver-level memoization for toPrimitiveInteger.
    // Backends may cache the canonical-RP → (PolyId, scale) mapping so the
    // driver's LCM/GCD scan + d&c build runs ONCE per unique RP per session.
    // T3 (SingleCellProjection instrumentation) proved step0/step1 each call
    // toPrimitiveInteger with the SAME RP across cells — the inner-mul cache
    // (S1+S1b) misses the driver itself. Default: no cache (caller pays full
    // driver cost every call).
    // ------------------------------------------------------------------
    virtual std::optional<std::pair<PolyId, mpq_class>>
        tpiCacheLookup(const RationalPolynomial&) const { return std::nullopt; }
    virtual void
        tpiCacheStore(const RationalPolynomial&, PolyId, const mpq_class&) {}
};

/**
 * Create the best available polynomial kernel.
 * Prefers LibPolyKernel if libpoly is compiled in; otherwise stub.
 */
std::unique_ptr<PolynomialKernel> createPolynomialKernel();

} // namespace xolver
