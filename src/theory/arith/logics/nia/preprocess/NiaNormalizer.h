#pragma once

#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "theory/core/TheorySolver.h"
#include <vector>
#include <optional>

namespace xolver {

// ActiveNiaConstraint is defined in NiaSolver.h, but we define it here
// for use by normalizer and other components.
struct ActiveNiaConstraint {
    PolyId poly;
    Relation rel;       // effective relation
    SatLit reason;
};

struct NormalizedNiaConstraint {
    PolyId poly;      // integer coefficients, always p rel 0 form
    Relation rel;     // Eq, Neq, Leq, Geq only
    SatLit reason;
};

/**
 * NiaNormalizer: transforms active constraints into normalized form.
 *
 * Rules:
 * 1. Effective relation already computed by assertLit (negateRelation applied).
 * 2. Clear denominators: multiply by positive LCM of all coefficients.
 * 3. Strict inequality normalization:
 *    Gt (p > 0) → p >= 1
 *    Lt (p < 0) → p <= -1
 * 4. Output: p rel 0 where rel ∈ {Eq, Neq, Leq, Geq}.
 */
class NiaNormalizer {
public:
    explicit NiaNormalizer(PolynomialKernel& kernel);

    std::optional<std::vector<NormalizedNiaConstraint>>
    normalize(const std::vector<ActiveNiaConstraint>& active);

    // Normalize a single active constraint. The result is a pure function of
    // `c` (clear-denominators + strict-inequality rewrite, no cross-constraint
    // state), so callers may cache it per constraint — see NiaSolver's
    // incremental normalize cache.
    NormalizedNiaConstraint normalizeOne(const ActiveNiaConstraint& c);

private:
    PolynomialKernel& kernel_;

    // Clear denominators of polynomial coefficients, return new poly with integer coefficients.
    PolyId clearDenominators(PolyId poly);

    // Normalize strict inequalities for integer domain.
    // Gt → Geq with adjusted polynomial, Lt → Leq with adjusted polynomial.
    NormalizedNiaConstraint normalizeStrict(const ActiveNiaConstraint& c, PolyId intPoly);
};

} // namespace xolver
