#pragma once

#include "theory/arith/nia/NiaTypes.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <gmpxx.h>
#include <vector>

namespace xolver {

/**
 * A per-variable congruence  var ≡ residue (mod modulus), justified by `reason`.
 * In production these are derived from the merged ModEqConstFact list:
 * `(mod x m) = c`  =>  x ≡ c (mod m). Kept as a plain value here so the modular
 * kernel is unit-testable without the ExprId/CoreIr plumbing.
 */
struct DioCongruence {
    VarId var;
    mpz_class residue;   // 0 <= residue < modulus
    mpz_class modulus;   // > 0
    SatLit reason;
};

/**
 * DioReasoner: the MISSING piece of NIA integer refutation — SYMBOLIC modular
 * congruence reasoning over linear equalities, for the QF_(A)NIA-unsat cluster
 * (AutomizerLoopAcceleration in-de42/ddlm2013/lcm2) that z3 refutes via
 * dio-tighten but xolver currently bit-blasts (non-terminating).
 *
 * NOT a re-implementation of GCD/SNF: single-equation GCD is GcdDivisibilityReasoner
 * and cross-equation Smith-NF is IntLinearEqualityCoreHNF (presolve). What is
 * missing is the COMPOSITION of linear equalities with large-modulus congruences:
 * for a linear equality `Σ aᵢ·xᵢ + c₀ = 0` whose variables carry congruences
 * `xᵢ ≡ rᵢ (mod m)`, the equality forces `Σ aᵢ·rᵢ + c₀ ≡ 0 (mod m)`; if that
 * residue is nonzero the system has no integer solution ⇒ UNSAT.
 *
 * Unlike ModularResidueReasoner (which ENUMERATES residues and is capped at a
 * modulus of 2^18), this is purely SYMBOLIC and handles arbitrary moduli such as
 * 2^32 in O(terms). Sound: integer vars, exact modular arithmetic, Conflict only.
 *
 * FUTURE: derive the congruences via linear elimination (so e.g. z9's congruence
 * follows from a chain), and conflict a derived equality against an active
 * disequality (the in-de42 ite-lowered shape).
 */
class DioReasoner {
public:
    explicit DioReasoner(PolynomialKernel& kernel);

    NiaReasoningResult run(const std::vector<NormalizedNiaConstraint>& constraints,
                           const std::vector<DioCongruence>& congruences);

private:
    PolynomialKernel& kernel_;
};

} // namespace xolver
