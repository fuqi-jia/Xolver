#pragma once
#include "expr/types.h"
#include <unordered_set>
#include <cstddef>

namespace zolver {

class CoreIr;
class SharedTermRegistry;

// ---------------------------------------------------------------------------
// Demand-driven care set for Nelson-Oppen combination (ZOLVER_COMB_CAREGRAPH).
//
// A shared term is "care-relevant" iff merging it (or splitting an arrangement
// on it) can trigger a theory inference: it appears as an argument of a
// UFApply / Select / Store / ConstArray, or as an operand of an Eq / Distinct,
// or it is a Purifier-internal bridge variable (which stands in for an alien
// UF/array-read term). A shared-term pair where NEITHER endpoint is
// care-relevant is inert — merging the two fires no congruence or array axiom
// and creates no interface conflict that was not already observable — so the
// combination layer may skip it when guessing interface (dis)equalities or
// arrangement splits.
//
// This is an UNDER-approximation prune. Skipping a pair can only lose
// completeness: a globally-inconsistent assignment can survive each theory's
// local check and is then caught by ModelValidator (Sat -> Unknown). It can
// NEVER produce a wrong UNSAT, because not splitting / not propagating a fact
// cannot create a conflict. (Charter soundness note: under-approximation safe,
// over-approximation dangerous.)
// ---------------------------------------------------------------------------
class CareGraph {
public:
    // Scan the (purified) assertions once and mark care-relevant shared terms.
    void build(const CoreIr& ir, const SharedTermRegistry& reg);

    bool built() const { return built_; }

    // When not built (flag OFF / never constructed), conservatively reports
    // EVERY term as cared, so callers behave identically to the pre-care-graph
    // code path.
    bool cares(SharedTermId t) const {
        return !built_ || care_.count(t) != 0;
    }

    // A pair is worth considering if either endpoint can trigger an inference.
    bool caresPair(SharedTermId a, SharedTermId b) const {
        return cares(a) || cares(b);
    }

    size_t careCount() const { return care_.size(); }

    void clear() {
        care_.clear();
        built_ = false;
    }

private:
    std::unordered_set<SharedTermId> care_;
    bool built_ = false;
};

} // namespace zolver
