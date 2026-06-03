#pragma once

// MCSatTrail — alternating Boolean and theory-variable trail for MCSAT.
//
// In CDCL(T) the SAT solver and theory keep separate trails synchronized
// at every check(). In MCSAT a SINGLE trail interleaves both:
//
//   level 0:  []
//   level 1:  BoolDecision(b1)
//             BoolPropagation(b2)            reasons={b1}
//   level 2:  TheoryDecision(x = 3/2)
//             TheoryPropagation(y = -7)      reasons={b1, b2}
//   level 3:  TheoryDecision(z = √2)
//
// The trail is LIFO under backtrack. Lookups (bool-by-SatVar or value-by-
// VarId) are O(1) via secondary index maps that the trail keeps in sync
// with `entries_`.

#include "experimental/mcsat/MCSatTypes.h"
#include <optional>
#include <unordered_map>
#include <vector>

namespace xolver {
namespace mcsat {

class MCSatTrail {
public:
    MCSatTrail() = default;

    // ----- Pushes ----------------------------------------------------------
    // A push is rejected (returns false) if the variable / SAT atom is
    // already bound on the trail. The caller is responsible for backtracking
    // before reasserting.
    bool pushBoolDecision(SatLit lit, int level);
    bool pushBoolPropagation(SatLit lit, int level, std::vector<SatLit> reasons);
    bool pushTheoryDecision(VarId var, RealValue value, int level);
    bool pushTheoryPropagation(VarId var, RealValue value, int level,
                               std::vector<SatLit> reasons);

    // ----- Backtrack -------------------------------------------------------
    // Drops every entry with `entry.level > targetLevel`, in LIFO order.
    void backtrackToLevel(int targetLevel);

    // Empty trail (level → 0, all assignments dropped).
    void clear();

    // ----- Lookups (O(1)) --------------------------------------------------
    // Returns the assigned polarity of SAT variable v on the current trail,
    // or nullopt if v is unbound.
    std::optional<bool> lookupBool(SatVar v) const;

    // Returns a pointer to the assigned value of arithmetic variable v on
    // the current trail, or nullptr if v is unbound. Pointer remains valid
    // until the next mutation of the trail.
    const RealValue* lookupVar(VarId v) const;

    // ----- Iteration -------------------------------------------------------
    const std::vector<TrailEntry>& entries() const { return entries_; }
    size_t size() const { return entries_.size(); }
    bool empty() const { return entries_.empty(); }

    // The level of the entry most recently pushed, or 0 if empty.
    int topLevel() const;

private:
    // Pushing helpers
    bool indexBool_(SatLit lit, size_t idx);
    bool indexVar_(VarId v, size_t idx);
    void unindexEntry_(const TrailEntry& e);

    std::vector<TrailEntry> entries_;
    std::unordered_map<SatVar, size_t> boolIndex_;  // SatVar → entries_ idx
    std::unordered_map<VarId, size_t> varIndex_;    // VarId  → entries_ idx
};

} // namespace mcsat
} // namespace xolver
