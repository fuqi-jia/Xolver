#pragma once

// MCSAT — shared types for the MCSAT framework.
//
// MCSAT (Model-Constructing SAT) is an alternative to CDCL(T)/CDCAC in which
// the SAT solver and the theory share a SINGLE trail that interleaves Boolean
// and theory variable assignments. The framework here is generic; per-theory
// behaviour (which value to pick, how to explain a conflict) is supplied by
// an MCSatEngine subclass in `src/theory/arith/<theory>/{nlsat,mcsat}/`.
//
// Soundness invariants (mirroring docs/agents/NLSAT-plan.md §15):
//   - A theory-decision value is NEVER materialized as a SAT literal.
//   - A SAT-level conflict clause emitted by MCSAT must be theory-valid
//     (true in every model). The MCSatEngine::explainConflict contract
//     forbids returning a clause that mentions an undecided Boolean atom
//     except via a fresh variable-bound disjunct produced by the engine.
//   - The framework NEVER returns Sat without delegating to MCSatEngine::validateModel
//     against the original assertions.

#include "expr/types.h"
#include "sat/SatSolver.h"
#include "util/RealValue.h"
#include <cstdint>
#include <vector>

namespace xolver {
namespace mcsat {

// Kind of a single entry on the alternating M-trail.
//
// BoolDecision      — SAT solver decided a Boolean literal (asserted true).
// BoolPropagation   — SAT solver propagated a Boolean literal under a clause
//                     of asserted reasons.
// TheoryDecision    — Theory engine decided a value for an arithmetic
//                     variable (the value is feasible w.r.t. current trail).
// TheoryPropagation — Theory engine concluded that a variable's value is
//                     forced (e.g. a singleton feasible set).
enum class TrailEntryKind : uint8_t {
    BoolDecision,
    BoolPropagation,
    TheoryDecision,
    TheoryPropagation,
};

// A single entry on the M-trail. The struct is intentionally flat (fields
// that don't apply to a given kind are simply unused) — variant-based
// designs complicate iteration and serialization without measurable gain
// at the M-trail's scale (≤ a few thousand entries per check).
struct TrailEntry {
    TrailEntryKind kind = TrailEntryKind::BoolDecision;
    int level = 0;

    // Valid only when kind ∈ {BoolDecision, BoolPropagation}.
    SatLit lit{};

    // Valid only when kind ∈ {TheoryDecision, TheoryPropagation}.
    VarId var = NullVar;
    RealValue value{};

    // Reason chain: original SAT literals whose joint truth justifies this
    // entry. Decisions carry an empty reason. Propagations (Boolean or
    // theory) carry a non-empty reason — this is what `explainConflict`
    // unrolls when producing a theory-valid clause.
    std::vector<SatLit> reasonLits;
};

} // namespace mcsat
} // namespace xolver
