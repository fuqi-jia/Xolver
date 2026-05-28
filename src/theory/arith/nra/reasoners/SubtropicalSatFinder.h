#pragma once

#include "expr/types.h"   // VarId, Relation
#include <gmpxx.h>
#include <unordered_map>
#include <utility>
#include <vector>

namespace xolver {

// ============================================================================
// Subtropical satisfiability — a cheap, INCOMPLETE SAT-side heuristic for
// conjunctions of polynomial constraints (SMT-RAT / Fontaine-Ogawa-Sturm-Vu).
//
// Idea: substitute  x_i = s_i * B^{a_i}  with B -> +infinity, s_i in {+1,-1},
// a_i an integer "direction". A monomial  c * prod x_i^{e_i}  then scales as
//   sign(c) * (prod s_i^{e_i}) * B^{<e,a>},
// so the term with the unique largest <e,a> DOMINATES for large B. If we can
// pick a single shared direction a and a shared sign vector s such that, for
// every constraint, the dominating term carries the relation's required sign,
// then x_i = s_i * B^{a_i} satisfies the whole system for B large enough.
//
//   - direction a : a linear-programming feasibility problem (exact, ration­al
//                   Fourier-Motzkin), one row  <e_f - e_g, a> >= 1  per
//                   non-frame monomial g of each constraint (frame f dominates
//                   with an integer margin).
//   - signs   s   : a GF(2) parity system. The signed value of frame f is
//                   sign(c_f) * (-1)^{<e_f, sigma>} (s_i = (-1)^{sigma_i}); the
//                   relation fixes that to +1 or -1, i.e. a parity equation
//                   <e_f, sigma> = b_f (mod 2).  (Disequations impose none.)
//   - frame choice: which monomial dominates each constraint is discrete; a
//                   small backtracking search picks one per constraint, pruned
//                   by LP-feasibility and GF(2)-consistency.
//
// This finder is INCOMPLETE (it only reasons about behaviour at infinity, in a
// chosen orthant, and bails on equalities / over caps) and produces only a
// CANDIDATE. The caller MUST exact-validate the materialized assignment against
// the original constraints before reporting SAT (invariant 1). Soundness does
// not depend on the correctness of the LP / parity search at all.
//
// The API is deliberately kernel-free (pure exponent/coefficient data) so it
// can be unit-tested without a polynomial backend.
// ============================================================================

// One monomial of a constraint polynomial: integer coefficient (sign and
// magnitude both matter) and its exponent vector. An empty `powers` is the
// constant term.
struct SubtropicalMonomial {
    mpz_class coeff;                              // must be non-zero
    std::vector<std::pair<VarId, int>> powers;    // (var, exponent>0); sorted not required
};

// One constraint: `monomials` (relation) 0. Supported relations: Gt, Geq, Lt,
// Leq, Neq. An Eq constraint makes the system unsupported (a non-zero dominating
// term can never be zero at infinity).
struct SubtropicalConstraint {
    std::vector<SubtropicalMonomial> monomials;
    Relation rel;
};

// A subtropical witness DIRECTION: per-variable integer exponent a_i and sign
// s_i. Variables absent from these maps default to exponent 0 / sign +1.
struct SubtropicalDirection {
    std::unordered_map<VarId, mpz_class> exponents;  // a_i
    std::unordered_map<VarId, int> signs;            // s_i in {+1,-1}
};

struct SubtropicalResult {
    bool found = false;        // a direction was found
    bool unsupported = false;  // bailed early (equality / over caps); informational
    SubtropicalDirection dir;
};

class SubtropicalSatFinder {
public:
    struct Config {
        int maxVars = 16;           // skip the whole attempt above this
        int maxConstraints = 64;
        int maxMonomials = 256;     // total across all constraints
        long fmRowCap = 20000;      // Fourier-Motzkin row blow-up guard
        long searchNodeCap = 50000; // frame-backtracking node budget
    };

    SubtropicalSatFinder() = default;
    explicit SubtropicalSatFinder(Config cfg) : cfg_(cfg) {}

    // Search for a witness direction. CANDIDATE ONLY — caller must validate the
    // materialized assignment exactly.
    SubtropicalResult find(const std::vector<SubtropicalConstraint>& constraints,
                           const std::vector<VarId>& vars) const;

    // Build a concrete rational assignment  x_i = s_i * base^{a_i}  from a
    // direction. `base` should be an integer > 1. Variables in `vars` not pinned
    // by the direction get value s_i * 1 = +1.
    static std::unordered_map<VarId, mpq_class>
    materialize(const SubtropicalDirection& dir,
                const std::vector<VarId>& vars,
                const mpq_class& base);

private:
    Config cfg_;
};

} // namespace xolver
