#pragma once

#include "util/RealValue.h"

#include <gmpxx.h>
#include <optional>
#include <vector>

namespace xolver {

// ============================================================================
// CAC covering data structures (lever 3, module A — see ../CAC.md).
//
// A `Covering` is the union of EXCLUDED intervals on a single CAC axis: the
// cells that conflict-driven coverings has already ruled out for the current
// variable. The two operations the get_unsat_cover recursion needs are:
//   * sampleUncovered() — a real point in a remaining gap (the next x_i to try),
//                         or nullopt when the union already covers all of ℝ;
//   * isComplete()      — the union covers ℝ (⇒ the level is UNSAT).
//
// Endpoints are exact `ExtendedRealValue` (RealValue ∪ {±∞}), so cell boundaries
// that are algebraic numbers (roots of projection polynomials) are represented
// exactly. All reasoning is exact (RealValue::compare is a decision procedure).
// Pure data structures — no kernel/engine dependency — so they are unit-tested
// in isolation.
// ============================================================================

// One connected interval of ℝ with open/closed endpoint flags. The open/closed
// bit is ignored for an infinite endpoint (±∞ is never a member).
struct CacInterval {
    ExtendedRealValue lo;
    ExtendedRealValue hi;
    bool loOpen = true;
    bool hiOpen = true;

    static CacInterval all() {
        return {ExtendedRealValue::negInf(), ExtendedRealValue::posInf(), true, true};
    }
    static CacInterval point(RealValue v) {
        auto e = ExtendedRealValue::finite(std::move(v));
        return {e, e, false, false};
    }
    // (lo, hi) with the given openness. Either endpoint may be ±∞.
    static CacInterval make(ExtendedRealValue lo, ExtendedRealValue hi,
                            bool loOpen, bool hiOpen) {
        return {std::move(lo), std::move(hi), loOpen, hiOpen};
    }

    // A well-formed nonempty interval: lo < hi, or lo == hi closed on both sides
    // (a single point). Both endpoints finite for the point case.
    bool valid() const;
    // Is the real value x a member of this interval?
    bool contains(const RealValue& x) const;
};

class Covering {
public:
    void add(const CacInterval& iv);            // ignores invalid/empty intervals
    void clear() { intervals_.clear(); }

    bool covers(const RealValue& x) const;      // x ∈ some interval
    // A real point not covered by the union, or nullopt iff the union == ℝ.
    // Prefers a rational sample; returns an exact (possibly algebraic) point only
    // for an isolated point-gap between two intervals open at a shared endpoint.
    std::optional<RealValue> sampleUncovered() const;
    bool isComplete() const;                    // union covers all of ℝ

    const std::vector<CacInterval>& intervals() const { return intervals_; }
    size_t size() const { return intervals_.size(); }

private:
    std::vector<CacInterval> intervals_;
    // Disjoint maximal intervals sorted left→right (open/closed-aware merge).
    std::vector<CacInterval> merged() const;
};

// A rational q with a < q < b. Precondition: a < b. Exposed for reuse/testing.
mpq_class rationalStrictlyBetween(const RealValue& a, const RealValue& b);

} // namespace xolver
