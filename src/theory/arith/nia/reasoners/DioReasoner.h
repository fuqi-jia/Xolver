#pragma once

#include "theory/arith/nia/NiaTypes.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/presolve/IntegerLinearAlgebra.h"
#include <gmpxx.h>
#include <map>
#include <optional>
#include <string>
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
 * A variable's integer bounds with the literals that justify them — fed to the
 * lattice-tightening path (tightenConflict) so the bound hull's contribution to
 * a conflict is soundly explained.
 */
struct DioVarBound {
    bool hasLo = false, hasHi = false;
    mpz_class lo, hi;
    std::vector<SatLit> loReasons, hiReasons;
};

/**
 * A normalized integer linear form  Σ coeff·var + cst  (relation against 0 given
 * by the list it lives in), with the literal that justifies the source atom.
 * String-keyed so both LIA (LinearFormKey) and NIA can build it from their own
 * representation and share the one tightening implementation.
 */
struct DioLinForm {
    std::vector<std::pair<std::string, mpz_class>> coeffs;
    mpz_class cst;
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

    /**
     * Lattice-tightening refutation (arith-dio-tighten) over already-normalized
     * integer data. Builds the equalities into A·x = b, then for each disequality
     * `form ≠ 0` tests whether the equality lattice + the per-variable bounds
     * force `form` to 0 (latticeForcesFormZero). Returns, for the first such
     * disequality, the conflict literals = the equalities' reasons + that
     * disequality's reason + the bound literals of the form's variables; or
     * nullopt if nothing is forced. Pure and string-keyed so LIA and NIA share it.
     */
    static std::optional<std::vector<SatLit>> tightenConflict(
        const std::vector<DioLinForm>& eqs,
        const std::vector<DioLinForm>& neqs,
        const std::map<std::string, DioVarBound>& bounds);

    /**
     * Pure lattice-step + bound-tightening core (z3's arith-dio-tighten).
     *
     * Given an integer equality system A·x = b over columns [0,n), optional
     * per-column bounds lo[j]/hi[j] (nullopt = unbounded), and a linear form
     * `Σ formW[j]·x_j + formC`, return true iff EVERY integer solution of
     * (A x = b ∧ lo ≤ x ≤ hi) has form(x) = 0 — equivalently, asserting the
     * disequality `form ≠ 0` on top is UNSAT. (Vacuously true, hence sound,
     * when the equalities+bounds are themselves infeasible.)
     *
     * Mechanism: from U·A·V = D (Smith Normal Form) recover a particular
     * solution x0 and the kernel columns V[:,free]; the form's achievable
     * values are a SUBSET of (A0 + g·ℤ) ∩ [Lmin,Lmax], with A0 = form(x0),
     * g = gcd over free cols f of Σ_k formW[k]·V[k][f], and [Lmin,Lmax] the
     * per-variable bound hull. The subset relation makes a positive verdict
     * sound despite the hull over-approximation. Returns false (never a false
     * conflict) whenever a form variable is unbounded or the system is empty.
     */
    static bool latticeForcesFormZero(
        const IntMatrix& A,
        const std::vector<mpz_class>& b,
        const std::vector<std::optional<mpz_class>>& lo,
        const std::vector<std::optional<mpz_class>>& hi,
        const std::vector<mpz_class>& formW,
        const mpz_class& formC);

private:
    PolynomialKernel& kernel_;
};

} // namespace xolver
