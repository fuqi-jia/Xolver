// Farkas-Or Phase 1: branch feasibility under a fixed bounded assignment.
//
// Given:
//   - a FarkasBranch (lambdas, equalities, inequalities classified by P0)
//   - a concrete assignment B for bounded global vars
//   - the set of CT-like (unbounded cost) vars
// produce zero or more BranchCandidates: each is a non-negative integer ray
// over the branch's λ-vars + a CT-interval / residual-LIA constraint that
// must hold for the candidate to actually satisfy the branch's inequalities.
//
// Algorithm: deterministic SUPPORT ENUMERATION over subsets of λ-vars. For
// each support S, build A_S(B) ∈ Q^{m × |S|} from the branch's equalities,
// compute the Q-nullspace, scale the rational ray to a primitive non-negative
// integer ray, then run the inequality classifier under that ray to derive
// the CT interval and scale.
//
// Soundness: this routine returns CANDIDATES — Phase 2 (GAC) picks one per
// block, Phase 3 (residual LIA) checks the joint LIA feasibility, Phase 4
// validates the full integer model against the ORIGINAL CoreIr formula. P1
// alone never claims SAT or UNSAT.

#pragma once

#include "expr/ir.h"
#include "theory/arith/nia/farkas/FarkasOrTypes.h"
#include <gmpxx.h>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace xolver::farkas {

// A CT bound derived from a branch's inequality under a specific λ-ray and B.
// Two forms:
//   (a) Interval [ctLo, ctHi] on a single CT-like variable (most common).
//   (b) "All-cost-vars residual": multiple CT-like variables appear linearly
//       in the inequality. Returned as a residual LinearConstraint that the
//       Phase 3 LIA solver handles.
struct CtBound {
    bool       hasInterval = false;     // (a) form
    mpq_class  ctLo;                    // inclusive
    mpq_class  ctHi;
    bool       ctLoFinite = false;
    bool       ctHiFinite = false;
    std::string ctVar;                  // name of the single CT-like var

    // (b) residual form: coefficients of CT-like vars + constant + relation.
    // sum(coef * var) + c rel 0 must hold (rel is Geq for Stroeder strict
    // turned into non-strict by integer adjustment).
    std::unordered_map<std::string, mpq_class> residualCoefs;
    mpq_class residualConst = 0;
    enum class Rel { Geq, Leq, Eq, Trivial /*always-true*/ };
    Rel residualRel = Rel::Trivial;
};

struct BranchCandidate {
    int branchIndex = -1;                        // index into FarkasOrBlock::branches
    std::vector<std::string> lambdaNames;        // same as branch.lambdas
    std::vector<mpz_class>   lambdaRay;          // primitive non-negative integer ray
    int scaleT = 1;                              // multiplier; final λ = scaleT · ray
    std::vector<CtBound> ctBounds;               // one per branch inequality
    // Residual co-var assignments used to make the branch feasible. These
    // are non-λ non-B non-CT vars (e.g. Stroeder's RFN1_main_x, RFN1_CT)
    // that appear in branch atoms; we grid-enumerate them and the assembler
    // must commit to these specific values for the model to validate.
    std::unordered_map<std::string, mpz_class> residValues;
    // Trivial ray flag: the all-λ=0 candidate (equalities hold by constant
    // matching at this (B, resid); strict ineqs hold via residual+constant
    // alone, no λ contribution). Useful for branches whose strict ineq has
    // a free residual slack that already meets the > 0 threshold.
    bool trivialRay = false;
};

class FarkasOrBranchSolver {
public:
    explicit FarkasOrBranchSolver(const CoreIr& ir) : ir_(ir) {}

    // Top-level: solve a branch under bounded assignment B. Returns
    // candidates (possibly empty if no non-trivial ray exists).
    //
    // Two-tier strategy:
    //   1. Identify residual co-vars (non-λ non-B non-CT vars appearing
    //      in branch atoms — e.g. Stroeder's RFN1_main_x, RFN1_main_y,
    //      RFN1_CT inside the lam6+lam4+lam5 flattened branch). Grid-
    //      enumerate them.
    //   2. For each (B, resid) combo, call solveBranchCore. Also try the
    //      "trivial ray" λ=0 candidate when equalities and strict ineqs
    //      hold via residual + constant alone.
    std::vector<BranchCandidate> solveBranch(
        const FarkasBranch& branch,
        const std::unordered_map<std::string, mpz_class>& B,
        const std::vector<std::string>& ctVars) const;

    // Inner solver: original support-enumeration logic over a fixed
    // (B ∪ resid) substitution. Caller is responsible for grid iteration.
    std::vector<BranchCandidate> solveBranchCore(
        const FarkasBranch& branch,
        const std::unordered_map<std::string, mpz_class>& BAugmented,
        const std::vector<std::string>& ctVars) const;

private:
    const CoreIr& ir_;

    // Extract a single equality row: for each λ_j in `lambdas`, what's its
    // coefficient after substituting B? Returns the row vector (length =
    // |lambdas|) plus a constant term that must equal zero (or check
    // explicitly). Returns nullopt on shape failure.
    struct EqRow {
        std::vector<mpq_class> coeffs;   // size == |lambdas|
        std::unordered_map<std::string, mpq_class> residCoeffs;  // resid var → coef
        mpq_class constant = 0;          // poly constant after B substitution
    };
    std::optional<EqRow> extractEqRow(
        ExprId atomId,
        const std::vector<std::string>& lambdas,
        const std::unordered_map<std::string, mpz_class>& B,
        const std::unordered_set<std::string>& residCoVars = {}) const;

    // Same for an inequality atom: extract λ-coefficient row + the
    // CT-side (which is a linear function of CT-vars).
    // Three classes of monomials are tracked separately:
    //   lambdaCoeffs    pure λ terms (no CT factor):   c · λ_j
    //   ctCoeffs        pure CT terms (no λ factor):   c · CT
    //   bilinearCoeffs  λ·CT bilinears:                c · λ_j · CT
    // Under a ray substitution λ_j = ray[j], the bilinear contribution
    // (c·ray[j]) gets added to the ctCoeffs entry for the matching CT.
    struct IneqRow {
        std::vector<mpq_class> lambdaCoeffs;             // size == |lambdas|
        std::unordered_map<std::string, mpq_class> ctCoeffs;  // CT-var → coef
        std::unordered_map<std::string, mpq_class> residCoeffs;  // resid var → coef
        // bilinear[(lambdaIdx, ctVar)] = coefficient
        std::vector<std::tuple<int, std::string, mpq_class>> bilinearCoeffs;
        mpq_class constant = 0;
        enum class Rel { Geq, Gt, Leq, Lt, Eq } rel = Rel::Geq;
    };
    std::optional<IneqRow> extractIneqRow(
        ExprId atomId,
        const std::vector<std::string>& lambdas,
        const std::unordered_map<std::string, mpz_class>& B,
        const std::vector<std::string>& ctVars,
        const std::unordered_set<std::string>& residCoVars = {}) const;

    // Helpers: substitute B into a polynomial sub-expression, returning
    // a rational constant. If the sub-expression contains a CT-like var,
    // returns nullopt (caller should call the CT-aware variant).
    std::optional<mpq_class> evalUnderB(
        ExprId polyId,
        const std::unordered_map<std::string, mpz_class>& B) const;

    // Solve A_S · λ_S = 0 over Q, find a primitive non-negative integer
    // ray. Returns ray of length |S| or empty if infeasible / multiple rays.
    std::vector<mpz_class> findPrimitiveNonNegRay(
        const std::vector<std::vector<mpq_class>>& A_S) const;

    // Augmented Farkas solver (P1 v3 / task #151). Given:
    //   A_λ ∈ Q^{m × L}  (λ coefficients per equation)
    //   A_r ∈ Q^{m × R}  (residual coefficients per equation)
    //   c   ∈ Q^m        (RHS = -constants)
    // find (λ ∈ Z^L_≥0, r ∈ Z^R) such that A_λ·λ + A_r·r = c.
    //
    // Algorithm: build augmented matrix [A_r | A_λ | c] of size m × (R+L+1),
    // RREF with residual columns pivoted FIRST. After RREF:
    //   - r-pivot rows give r_i = (RHS) − Σ (coef · free vars)
    //   - λ-pivot rows give λ_j = (RHS) − Σ (coef · free vars)
    //   - pure-zero rows must have zero RHS (else infeasible)
    // Then enumerate free λ vars in a bounded integer range (0..maxFree);
    // for each enumeration, pivot λs and residuals are determined. If
    // pivot λs are non-neg integers, emit (λ, r) solution.
    //
    // Returns (λ, r) on success or empty λ on failure. residNames must
    // be in stable order matching the columns the caller uses.
    struct AugmentedSolution {
        std::vector<mpz_class> lambdaValues;
        std::unordered_map<std::string, mpz_class> residValues;
    };
    std::vector<AugmentedSolution> solveAugmentedFarkas(
        const std::vector<std::vector<mpq_class>>& A_lambda,
        const std::vector<std::vector<mpq_class>>& A_resid,
        const std::vector<mpq_class>& c,
        const std::vector<std::string>& residNames,
        std::size_t maxFreeRange = 30,
        std::size_t maxSolutions = 4) const;

    // P1 v2: solve A_S · λ_S = c over Q with λ ∈ Z^n_≥0. Handles both the
    // homogeneous (c = 0, delegates to findPrimitiveNonNegRay) and the
    // non-homogeneous (c ≠ 0, particular solution + 1D nullspace combine)
    // cases. Returns ray of length |S| or empty if no non-neg integer
    // solution exists / shape unsupported.
    //
    // Algorithm for non-homogeneous case:
    //   1. RREF the augmented matrix [A_S | c].
    //   2. Inconsistency check (zero row with non-zero RHS → empty).
    //   3. Build particular solution (free vars = 0; pivot vars from RREF).
    //   4. If 0 free vars (unique solution): check non-neg integer particular.
    //   5. If 1 free var: bounded enumeration of t such that particular +
    //      t·homog is non-neg integer (handles small Farkas certificates).
    std::vector<mpz_class> findNonNegIntegerSolution(
        const std::vector<std::vector<mpq_class>>& A_S,
        const std::vector<mpq_class>& c) const;

    // From an IneqRow and a λ-ray, derive a CtBound. Substitutes λ = ray
    // (scaled by t) into the row; collects CT coefficients, derives the
    // bound interval.
    CtBound deriveCtBound(
        const IneqRow& row,
        const std::vector<mpz_class>& ray,
        const std::vector<std::string>& lambdaNames) const;
};

} // namespace xolver::farkas
