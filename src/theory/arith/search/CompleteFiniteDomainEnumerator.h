#pragma once

// Capability 9 — Complete Finite Domain Enumerator.
//
// After the theory-check presolve fixpoint, if every original variable is
// either (a) substituted (reconstructable from substMap) or (b) bounded to a
// finite Int IntervalSet, this enumerates the Cartesian product of the free
// (bounded) variables, reconstructs the substituted ones, and:
//   - returns SAT with a full model the moment IntegerModelValidator confirms
//     it against the ORIGINAL normalized constraints (validator-gated);
//   - returns UnsatComplete once the entire (≤ MaxFiniteDomainSize) product is
//     exhausted with no validating candidate, with a reason covering every
//     active constraint and bound.
//   - returns NotApplicable when the gating fails (some var unbounded and
//     un-substituted, or the product exceeds the size cap).

#include "theory/arith/presolve/Presolve.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"

#include <vector>

namespace xolver {

struct FiniteDomainResult {
    enum class Status { Sat, UnsatComplete, NotApplicable } status = Status::NotApplicable;
    IntegerModel model;        // valid when Sat
    TheoryConflict conflict;   // valid when UnsatComplete
};

class CompleteFiniteDomainEnumerator {
public:
    static constexpr size_t kMaxFiniteDomainSize = 4096;

    static FiniteDomainResult run(const PresolveState& st,
                                  const std::vector<NormalizedNiaConstraint>& normalized,
                                  const IntegerModelValidator& validator,
                                  PolynomialKernel& kernel);
};

} // namespace xolver
