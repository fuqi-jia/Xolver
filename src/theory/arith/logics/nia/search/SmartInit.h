#pragma once

#include "theory/arith/logics/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/logics/nia/preprocess/VariablePartition.h"
#include "theory/arith/logics/nia/core/DomainStore.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "theory/arith/logics/nia/search/IntegerModelValidator.h"  // IntegerModel
#include <gmpxx.h>
#include <random>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

/**
 * SmartInit (LS-SMART-1, user 2026-06-02 directive).
 *
 * Replace LS's blind random-±2000 (or random-±100) init with a
 * constraint-aware proposal. User example:
 *     x + y = 1, x + 2y = 4
 *     random sample x=1 -> y=1 (violates first eq)
 *     smart: solve linear subsystem -> x = -2, y = 3 (exact, both eqs hold)
 *
 * Three phases per init:
 *   1. PIN — single-var linear Eq atoms `c*v + k = 0` with c|k:
 *      pin v = -k/c.
 *   2. DERIVE — 2-var linear Eq atoms `c1*v1 + c2*v2 + k = 0` with
 *      |c_anchor| = 1: classify v_anchor as derived from v_dep. The
 *      derived value is cascade-evaluated using v_dep's current value.
 *   3. SMART SAMPLE — free vars (neither pinned nor derived). For each:
 *      a. Bound-tighten from single-var inequalities (Geq, Leq).
 *      b. Modular pre-check via coefficient GCD (if some atom forces
 *         v ≡ k (mod g), respect it during sample).
 *      c. Sample from the resulting feasible set (small range first;
 *         expand if necessary).
 *
 * Soundness: SmartInit's output is a CANDIDATE assignment. The LS
 * validates any SAT it claims via IntegerModelValidator. SmartInit
 * never asserts UNSAT — it only proposes a starting point.
 *
 * Gated by XOLVER_NIA_LS_SMART_INIT (default-OFF). When the LS asks
 * SmartInit for an init proposal, the proposal supersedes the random
 * branch for free vars; pinned/derived vars are set deterministically.
 */
struct SmartInitVarInfo {
    bool pinned = false;
    mpz_class pinnedValue = 0;

    bool derived = false;
    int anchorSign = 1;  // ±1 (sign of the anchor's coefficient)
    mpz_class derivedConst = 0;
    // dependency vars + their coefficients in the defining atom.
    std::vector<std::pair<std::string, mpz_class>> derivedDeps;

    // Tightened bound (intersection with DomainStore + derived from
    // single-var inequalities). Empty bounds = no constraint.
    bool hasLower = false;
    bool hasUpper = false;
    mpz_class lower = 0;
    mpz_class upper = 0;

    // Modular pre-check: residue set v mod modulus. Empty modulus means
    // no modular constraint detected; nonzero modulus means
    // v ≡ allowedResidues[i] (mod modulus) for some i. When LS samples
    // a value, it picks one residue then shifts by k*modulus.
    mpz_class modulus = 0;  // 0 = unset
    std::vector<mpz_class> allowedResidues;

    // LS-SMART-5: coefficient-derived sample range. For each atom
    // containing v with coefficient c_i and constant rhs_i, the
    // plausible-|v| upper bound is |rhs_i / c_i| (the value v would
    // need to balance the atom if all other vars were zero).
    // coefRange = max of these over all atoms; 0 = no useful bound.
    mpz_class coefRange = 0;
};

class SmartInit {
public:
    explicit SmartInit(PolynomialKernel& kernel);

    // Analyse constraints + bounds; produce per-var SmartInitVarInfo
    // covering pin / derive / bound / modular.
    void analyze(const std::vector<NormalizedNiaConstraint>& constraints,
                 const DomainStore& domains);

    // Build a proposed initial model. RNG provided by caller for
    // determinism + Reduces SmartInit's API to a pure function of
    // (analysis, rng).
    IntegerModel propose(std::mt19937_64& rng) const;

    // Snapshot for downstream consumers (HYB-X passes derived map to LS).
    const std::unordered_map<std::string, SmartInitVarInfo>& info() const {
        return info_;
    }

private:
    PolynomialKernel& kernel_;
    std::unordered_map<std::string, SmartInitVarInfo> info_;
    std::vector<std::string> varsInOrder_;  // deterministic iteration

    // Phase 1: walk constraints, extract linear-only structures.
    void extractLinearInfo(const std::vector<NormalizedNiaConstraint>& constraints);
    // Phase 2: tighten bounds from DomainStore + single-var inequalities.
    void tightenBounds(const std::vector<NormalizedNiaConstraint>& constraints,
                       const DomainStore& domains);
    // Phase 3: cascade-evaluate derived vars using current info_'s
    // pinned/sample values to fix the derived var's value.
    mpz_class evalDerived(const std::string& anchor,
                           const IntegerModel& cur) const;

    // Try-extract: is `poly` of the form (sum of c_i * v_i^1) + const?
    // Returns true with per-var coefficients + constant; false if any
    // non-linear monomial appears.
    bool isLinearForm(PolyId poly,
                      std::vector<std::pair<std::string, mpz_class>>& terms,
                      mpz_class& constTerm) const;
};

} // namespace xolver
