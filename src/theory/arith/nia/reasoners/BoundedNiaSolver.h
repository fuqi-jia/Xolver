#pragma once

#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include "theory/core/TheorySolver.h"

namespace xolver {

enum class BoundedSolveStatus {
    Sat,              // exact model found and validated
    UnsatComplete,    // complete enumeration: no model exists
    UnknownBudget,    // budget exhausted
    UnknownUnsupported // interval evaluation unsupported
};

struct BoundedSolveResult {
    BoundedSolveStatus status;
    std::optional<IntegerModel> model;
    std::optional<TheoryConflict> conflict;
};

/**
 * BoundedNiaSolver: complete solver for finite-domain NIA.
 *
 * - Direct enumeration for small domains
 * - Interval branch-and-bound for larger domains (skeleton)
 */
class BoundedNiaSolver {
public:
    explicit BoundedNiaSolver(PolynomialKernel& kernel);

    BoundedSolveResult solve(const std::vector<NormalizedNiaConstraint>& constraints,
                              const DomainStore& domains,
                              const IntegerModelValidator& validator,
                              TheoryLemmaStorage& lemmaDb);

    // Phase 3a partial bounded enumeration. Sound SAT-finding fallback for
    // systems where SOME variables are tightly bounded (`v ∈ [lo, hi]` with
    // small `hi-lo+1`) but OTHERS are unbounded. Enumerates the bounded
    // subset and, for each combination, tries a fixed set of candidate
    // values (`{0, 1, -1, lo+1, hi-1}` clipped to domain) for each
    // unbounded variable. Each candidate model is fully validated against
    // the original constraints via IntegerModelValidator before any SAT
    // claim — invariant 1 preserved.
    //
    // Soundness contract:
    //   - SAT verdict requires Valid from IntegerModelValidator (full
    //     evaluation over the candidate's variable assignment).
    //   - Never claims UNSAT (the unbounded vars' search space is not
    //     exhausted; an Unknown branch is returned instead).
    //   - Empty bounded subset → returns UnknownUnsupported (the existing
    //     enumerate() path already handles fully-bounded systems).
    //
    // Caller (NiaSolver::stageBounded) gates on
    // XOLVER_NIA_BOUNDED_PARTIAL=1 (default-OFF) and only invokes when
    // the full-domain check (domains.allFinite) failed.
    BoundedSolveResult solvePartial(
            const std::vector<NormalizedNiaConstraint>& constraints,
            const DomainStore& domains,
            const IntegerModelValidator& validator);

private:
    PolynomialKernel& kernel_;

    static const mpz_class ENUMERATION_THRESHOLD;
    // Tightness cap on what counts as "tightly bounded" for the partial
    // enumerator. A variable with `hi - lo + 1 ≤ this` enters the bounded
    // subset; larger ranges stay in the unbounded set. Picked small so the
    // cartesian product of bounded values stays well under
    // PARTIAL_BUDGET below.
    static const mpz_class PARTIAL_VAR_RANGE_CAP;
    // Cap on the cartesian product of bounded-subset values explored per
    // call. Keeps the worst case at O(this * guess_count^k) which is
    // bounded.
    static const mpz_class PARTIAL_BUDGET;

    BoundedSolveResult enumerate(const std::vector<NormalizedNiaConstraint>& constraints,
                                  const DomainStore& domains,
                                  const IntegerModelValidator& validator,
                                  const std::vector<std::string>& vars);
};

} // namespace xolver
