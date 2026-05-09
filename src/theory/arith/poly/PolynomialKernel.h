#pragma once

#include "expr/types.h"
#include "expr/ir.h"
#include <vector>
#include <memory>
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
