#pragma once

// MCSatEngine — abstract per-theory backend for the MCSAT framework.
//
// The framework (McsatSolver) owns the M-trail and the main decide /
// propagate / conflict loop. A concrete engine plugs in:
//
//   1. assertion handling — bookkeeping per theory atom received from SAT;
//   2. value selection    — given the trail, pick a feasible value for a
//                           theory variable (or report no value exists);
//   3. propagation        — derive forced variable values from the trail;
//   4. conflict explain   — when a constraint becomes infeasible, produce
//                           a theory-valid clause (the MCSAT explanation
//                           function) that the SAT solver can learn;
//   5. model validation   — confirm a complete trail satisfies every
//                           original assertion before claiming SAT.
//
// NRA backend: `src/theory/arith/nra/nlsat/NlsatEngine` — real values via
//   libpoly's AlgebraBackend; explain via SingleCellProjection-style cell.
// NIA backend: `src/theory/arith/nia/mcsat/NiaMcsatEngine` — integer values;
//   explain combines real-relaxation cell projection and an integrality
//   split lemma whenever the relaxation returns a non-integral root.

#include "experimental/mcsat/MCSatTrail.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/core/TheorySolver.h"  // for TheoryModel
#include <optional>
#include <vector>

namespace xolver {
namespace mcsat {

// Outcome of an attempt to pick a value for a theory variable.
//
//   Found    — a feasible value was discovered and lives in `value`.
//   Conflict — every value is infeasible; `blockingAtoms` lists the
//              atoms that jointly produced the conflict, and the
//              framework will call explainConflict() to obtain a clause.
//   GiveUp   — the engine cannot decide (algebra-backend limitation,
//              budget exhaustion, etc.). The framework converts this
//              to TheoryCheckResult::Unknown; it is NEVER turned into
//              UNSAT. This is the soundness-floor exit per §15.6.
struct ValueChoice {
    enum class Kind : uint8_t { Found, Conflict, GiveUp };

    Kind kind = Kind::GiveUp;
    RealValue value{};                          // valid when kind == Found
    std::vector<TheoryAtomRecord> blockingAtoms; // valid when kind == Conflict
    std::string reason;                          // human-readable for GiveUp

    static ValueChoice found(RealValue v) {
        ValueChoice c;
        c.kind = Kind::Found;
        c.value = std::move(v);
        return c;
    }
    static ValueChoice conflict(std::vector<TheoryAtomRecord> atoms) {
        ValueChoice c;
        c.kind = Kind::Conflict;
        c.blockingAtoms = std::move(atoms);
        return c;
    }
    static ValueChoice giveUp(std::string why = {}) {
        ValueChoice c;
        c.kind = Kind::GiveUp;
        c.reason = std::move(why);
        return c;
    }
};

// A theory propagation that the engine forces at the current level.
struct TheoryPropagation {
    VarId var;
    RealValue value;
    std::vector<SatLit> reasons;  // asserted atom SAT lits justifying the forcing
};

class MCSatEngine {
public:
    virtual ~MCSatEngine() = default;

    // -------- Lifecycle hooks (called by the framework) ------------------

    // Fresh start (mirrors TheorySolver::reset).
    virtual void reset() = 0;

    // SAT asserted (atom = value) at decision level `level`, with SAT literal
    // `assertedLit`. The engine should index the atom for fast lookup.
    virtual void onAssertAtom(const TheoryAtomRecord& atom, bool value,
                              int level, SatLit assertedLit) = 0;

    // Backtrack: drop any atom-side state introduced above `targetLevel`.
    virtual void onBacktrack(int targetLevel) = 0;

    // -------- Decide / propagate ----------------------------------------

    // Return the next theory variable to decide, given the trail.
    // Return NullVar if the trail already assigns every theory variable
    // present in the current active set.
    virtual VarId pickNextVar(const MCSatTrail& trail) = 0;

    // Pick a value for `var` that satisfies every asserted atom currently
    // forced by the trail's partial assignment.
    virtual ValueChoice pickValue(VarId var, const MCSatTrail& trail) = 0;

    // Engine-side propagation: emit forced (var, value) entries justified by
    // the asserted atoms. Called by the framework after every SAT-side
    // push, before the next decide attempt. The default is no propagation.
    virtual std::vector<TheoryPropagation> propagate(const MCSatTrail& trail) {
        (void)trail;
        return {};
    }

    // -------- Conflict explanation --------------------------------------

    // Produce an MCSAT explanation clause: a set of SAT literals such that
    // their disjunction is theory-valid (true in every model), and at least
    // one literal in the disjunction is currently FALSE on the SAT trail
    // (so the clause forces backtrack on the SAT side).
    //
    // The `blockingAtoms` argument is the list returned by a previous
    // ValueChoice{ok=false}. Implementations should treat the SAT literals
    // attached to those atoms as the seed of the explanation, then refine
    // via projection / cell-construction.
    virtual std::vector<SatLit> explainConflict(
        const MCSatTrail& trail,
        const std::vector<TheoryAtomRecord>& blockingAtoms) = 0;

    // -------- Model output / validation ---------------------------------

    // Called by the framework once the trail assigns every relevant theory
    // variable. The engine must:
    //   (1) Evaluate every original assertion under the trail's value
    //       assignment using EXACT arithmetic;
    //   (2) If all original assertions are satisfied, populate `outModel`
    //       and return true;
    //   (3) Otherwise return false (the framework then asks for a
    //       conflict and backtracks).
    virtual bool validateModel(const MCSatTrail& trail,
                               TheorySolver::TheoryModel& outModel) = 0;
};

} // namespace mcsat
} // namespace xolver
