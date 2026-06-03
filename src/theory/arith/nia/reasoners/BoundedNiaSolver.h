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

    // Phase L1 step 3 — value-cache hint overload. Same algorithm as
    // solvePartial, but `hint` (when non-null and non-empty) is consulted
    // first for every variable's guess set. A cached LS bestAssignment
    // becomes the FIRST candidate tried, so a still-valid warm-start
    // returns Sat in O(1) validations instead of cartesian enumeration.
    //
    // Soundness: the hint values pass through IntegerModelValidator
    // identical to any other guess — never bypass validation. A stale or
    // bogus hint just causes one extra failed validation per variable.
    BoundedSolveResult solvePartialWithHint(
            const std::vector<NormalizedNiaConstraint>& constraints,
            const DomainStore& domains,
            const IntegerModelValidator& validator,
            const IntegerModel* hint);

private:
    PolynomialKernel& kernel_;

    // Caps that scale with remaining wall-clock when XOLVER_WALLCLOCK_SCALE is
    // enabled (default-inert: returns the env::paramLong base value otherwise).
    // Defaults exposed via env::paramLong so the autotuner sees them in
    // XOLVER_DUMP_PARAMS:
    //   XOLVER_NIA_BOUNDED_ENUM_THRESHOLD   (default 10000)
    //   XOLVER_NIA_BOUNDED_PARTIAL_RANGE_CAP (default 16)
    //   XOLVER_NIA_BOUNDED_PARTIAL_BUDGET    (default 4096)
    static mpz_class enumerationThreshold();
    static mpz_class partialVarRangeCap();
    static mpz_class partialBudget();

    BoundedSolveResult enumerate(const std::vector<NormalizedNiaConstraint>& constraints,
                                  const DomainStore& domains,
                                  const IntegerModelValidator& validator,
                                  const std::vector<std::string>& vars);
};

} // namespace xolver
