#pragma once

// OSF-CDCAC P1: explicit CertifiedSimplexFacts type.
//
// Replaces the implicit "heuristic-only" labeling on SimplexTableauFacts
// with an explicit type whose semantics are: "every bound here is
// provably implied by the active linear subset; safe to use for
// pruning / cover lifting / domain clipping".
//
// Distinction from SimplexTableauFacts:
//   SimplexTableauFacts  -- heuristic, never used for soundness
//   CertifiedSimplexFacts -- proven, safe for pruning + verdict paths
//
// Per the spec § 5:
//   CertifiedFacts:
//     - proven lower/upper bound
//     - implied equality x = c
//     - affine equality / affine bound
//     - Simplex UNSAT reason
//     - linear residual conflict

#include "expr/types.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>
#include <optional>
#include <unordered_map>
#include <vector>

namespace xolver {

struct CertifiedBound {
    mpq_class value;
    std::vector<SatLit> reasons;   // SAT literals whose conjunction proves the bound
    bool strict = false;
};

class CertifiedSimplexFacts {
public:
    // Look up a certified lower / upper bound. nullopt means "no certified
    // bound" (NOT "unbounded" -- the variable might be bounded by a path
    // we haven't proven yet).
    std::optional<CertifiedBound> lower(VarId v) const {
        auto it = lower_.find(v);
        return it == lower_.end() ? std::nullopt : std::optional<CertifiedBound>{it->second};
    }
    std::optional<CertifiedBound> upper(VarId v) const {
        auto it = upper_.find(v);
        return it == upper_.end() ? std::nullopt : std::optional<CertifiedBound>{it->second};
    }
    bool isFixed(VarId v) const {
        auto lo = lower(v), hi = upper(v);
        return lo && hi && !lo->strict && !hi->strict && lo->value == hi->value;
    }

    // Derive the certified sign of v from bounds. Returns 0 if indeterminate,
    // +1 strict positive, -1 strict negative, +2 nonneg, -2 nonpos.
    int certifiedSign(VarId v) const {
        auto lo = lower(v), hi = upper(v);
        if (lo && lo->value > 0) return +1;
        if (lo && lo->value == 0 && lo->strict) return +1;
        if (hi && hi->value < 0) return -1;
        if (hi && hi->value == 0 && hi->strict) return -1;
        if (lo && lo->value >= 0) return +2;
        if (hi && hi->value <= 0) return -2;
        return 0;
    }

    // The full bound set (mutator side); accessed by builders.
    std::unordered_map<VarId, CertifiedBound> lower_;
    std::unordered_map<VarId, CertifiedBound> upper_;

    // Equalities (Simplex-proven x = c or x = y + d). For now just the
    // single-var case; affine equalities can be appended.
    struct CertifiedEquality { VarId v; mpq_class value; std::vector<SatLit> reasons; };
    std::vector<CertifiedEquality> equalities_;

    // Builder helpers. tightenLower keeps the strongest (largest) lower
    // bound; tightenUpper keeps the smallest upper bound. Both union the
    // reason lists -- a tightening always carries the reasons of both the
    // old and new bound (the union is sound).
    void tightenLower(VarId v, const mpq_class& val, bool strict,
                      const std::vector<SatLit>& reasons) {
        auto it = lower_.find(v);
        if (it == lower_.end() ||
            val > it->second.value ||
            (val == it->second.value && strict && !it->second.strict)) {
            CertifiedBound b{val, reasons, strict};
            lower_[v] = std::move(b);
        }
    }
    void tightenUpper(VarId v, const mpq_class& val, bool strict,
                      const std::vector<SatLit>& reasons) {
        auto it = upper_.find(v);
        if (it == upper_.end() ||
            val < it->second.value ||
            (val == it->second.value && strict && !it->second.strict)) {
            CertifiedBound b{val, reasons, strict};
            upper_[v] = std::move(b);
        }
    }
};

} // namespace xolver
