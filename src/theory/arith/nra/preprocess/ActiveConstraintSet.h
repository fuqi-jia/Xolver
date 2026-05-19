#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "expr/types.h"
#include <vector>
#include <unordered_map>
#include <unordered_set>

namespace nlcolver {

// ------------------------------------------------------------------
// V5: ActiveConstraintSet — incremental constraint management
// Replaces the simple std::vector<ActiveConstraint> in CdcacSolver
// with level-indexed active list + polynomial index + lit mapping.
// ------------------------------------------------------------------

struct ActiveConstraintEntry {
    ConstraintId id = NullConstraintId;
    PolyId poly = NullPoly;
    Relation rel = Relation::Eq;
    SatLit reason{0, true};
    AtomId atom = NullAtom;
    int level = 0;
    bool isEC = false;       // V5: used as equational constraint
    bool isGuard = false;    // V5: used as guard polynomial
};

class ActiveConstraintSet {
public:
    void push();
    void pop(uint32_t n);
    void clear();

    void addConstraint(const ActiveConstraintEntry& entry);
    void removeConstraintsAboveLevel(int level);

    const std::vector<ActiveConstraintEntry>& entries() const { return entries_; }

    // Lookup by constraint ID
    const ActiveConstraintEntry* find(ConstraintId id) const;

    // Lookup by SAT literal
    const ActiveConstraintEntry* findByLit(SatLit lit) const;

    // Get all active polynomials (deduplicated)
    std::vector<PolyId> activePolys() const;

    // Get all active atoms (deduplicated)
    std::vector<AtomId> activeAtoms() const;

    // V5: Get equational constraints
    std::vector<ActiveConstraintEntry> equationalConstraints() const;

    size_t size() const { return entries_.size(); }
    bool empty() const { return entries_.empty(); }

private:
    std::vector<ActiveConstraintEntry> entries_;
    std::vector<size_t> scopeStack_;
    std::unordered_map<ConstraintId, size_t> idIndex_;
    std::unordered_map<uint32_t, size_t> litIndex_;  // SatLit.raw -> index
};

} // namespace nlcolver
