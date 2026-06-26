#pragma once

#include "theory/arith/logics/nia/reasoners/OmegaTest.h"   // reuse omega::Constraint (sparse int linear)
#include <gmpxx.h>
#include <map>
#include <vector>

namespace xolver::intprop {

// An integer interval domain for one variable. Absent flags ⇒ unbounded on that side.
struct Bound {
    bool hasLo = false, hasHi = false;
    mpz_class lo, hi;
};

enum class Result { Unsat, Ok };

// INTEGER interval bound propagation over the EQUALITY constraints of `cs`, seeded
// by `bounds` (var index → Bound). Runs a bounded fixpoint of integer interval
// contraction: for each equality `Σ aᵢxᵢ + c == 0` and each variable xⱼ in it,
// isolate aⱼ·xⱼ = −(Σ_{i≠j} aᵢxᵢ + c), bound the right-hand side from the other
// variables' current bounds, and tighten xⱼ to the INTEGER interval
// [⌈lo/aⱼ⌉, ⌊hi/aⱼ⌋] (sign-corrected). `bounds` is mutated IN PLACE and only ever
// tightened. Returns `Unsat` if any variable's domain becomes empty (lo > hi).
//
// SOUNDNESS: the tightening is an interval-contraction operator — every integer
// solution of `cs` consistent with the seed bounds stays within the tightened
// bounds (intersection preserves all solutions; floor/ceil are exact for integers).
// So `Unsat` is a genuine infeasibility and each tightened bound is entailed. This
// is the integer-PROPAGATION counterpart to the real ICP contraction (which does
// not round to integers) and to the Omega/modular REFUTATION (which only conflicts).
//
// Inequalities in `cs` are ignored here (this first cut handles equalities — the
// cleanest sign case); using only the equality subset is sound. Oversized systems
// bail early (no over-tightening; bounds left as-is).
Result propagate(const std::vector<omega::Constraint>& cs,
                 std::map<int, Bound>& bounds, int maxRounds = 16);

}  // namespace xolver::intprop
