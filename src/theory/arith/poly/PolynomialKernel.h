#pragma once

#include "expr/types.h"
#include "expr/ir.h"
#include <vector>
#include <memory>
#include <optional>
#include <unordered_map>
#include <gmpxx.h>

namespace nlcolver {

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
    // Factory / constants
    // ------------------------------------------------------------------
    virtual PolyId mkZero() = 0;
    virtual PolyId mkOne()  = 0;
    virtual PolyId mkConst(const mpq_class& c) = 0;
    virtual PolyId mkVar(std::string_view name) = 0;

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
    // Evaluation (for CAlC / sample checking)
    // ------------------------------------------------------------------
    virtual int sgn(PolyId a, const std::unordered_map<std::string, mpq_class>& sample) const = 0;

    // ------------------------------------------------------------------
    // Integer evaluation (for NIA exact validation)
    // ------------------------------------------------------------------
    // Evaluate polynomial at integer assignment (exact integer arithmetic).
    // Returns nullopt if evaluation is unsupported (e.g. stub backend).
    virtual std::optional<mpz_class> evalInteger(
        PolyId a,
        const std::unordered_map<std::string, mpz_class>& sample) const = 0;

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
    // Multivariate term decomposition (for GCD, interval evaluation, CAD)
    // ------------------------------------------------------------------
    struct MonomialTerm {
        mpz_class coefficient;                           // exact integer coefficient
        std::vector<std::pair<std::string, int>> powers; // [(var, exp), ...]; empty = constant term
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
};

/**
 * Create the best available polynomial kernel.
 * Prefers LibPolyKernel if libpoly is compiled in; otherwise stub.
 */
std::unique_ptr<PolynomialKernel> createPolynomialKernel();

} // namespace nlcolver
