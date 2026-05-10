#pragma once

#include "theory/TheorySolver.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include "theory/arith/nia/NiaNormalizer.h"
#include "theory/arith/nia/IntegerModelValidator.h"
#include "theory/arith/nia/DomainStore.h"
#include "theory/arith/nia/UnivariateIntegerReasoner.h"
#include "theory/arith/nia/LinearNiaDomainReasoner.h"
#include "theory/arith/nia/AlgebraicIntegerReasoner.h"
#include "theory/arith/nia/BoundedNiaSolver.h"
#include "theory/arith/nia/NiaLocalSearch.h"
#include "expr/types.h"
#include <gmpxx.h>
#include <vector>
#include <memory>
#include <optional>

namespace nlcolver {

/**
 * NIA (Nonlinear Integer Arithmetic) theory solver.
 *
 * NIA-Core pipeline:
 *   1. Normalize active constraints (clear denominators, strict → non-strict)
 *   2. Trivial constant handling
 *   3. Linear domain inference
 *   4. Univariate reasoning (RRT roots, square bounds)
 *   5. Algebraic reasoning (square, GCD, factor, modular)
 *   6. Empty domain check
 *   7. Bounded complete solver (enumeration / B&B)
 *   8. Local search heuristic
 *   9. Branch split lemma or Unknown
 */
class NiaSolver : public TheorySolver {
public:
    explicit NiaSolver(std::unique_ptr<PolynomialKernel> kernel);

    TheoryId id() const override { return TheoryId::NIA; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value,
                   int level, SatLit reason) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb) override;
    void reset() override;

private:
    struct NiaTrailEntry {
        int level;
        size_t activeSizeBefore;
    };

    struct PendingConflict {
        int level;
        TheoryConflict conflict;
    };

    struct PendingUnknown {
        int level;
    };

    std::unique_ptr<PolynomialKernel> kernel_;
    std::unique_ptr<PolynomialConverter> converter_;

    std::vector<ActiveNiaConstraint> active_;
    std::vector<NiaTrailEntry> trail_;
    std::optional<PendingConflict> pendingConflict_;
    std::optional<PendingUnknown> pendingUnknown_;

    // NIA-Core engines
    NiaNormalizer normalizer_;
    IntegerModelValidator validator_;
    DomainStore domains_;
    UnivariateIntegerReasoner univariate_;
    LinearNiaDomainReasoner linearDomain_;
    AlgebraicIntegerReasoner algebraic_;
    BoundedNiaSolver bounded_;
    NiaLocalSearch localSearch_;

    std::optional<IntegerModel> currentModel_;

    bool relationSatisfied(const mpq_class& val, Relation rel) const;
    std::optional<TheoryLemma> buildBranchLemma(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const DomainStore& domains,
        TheoryLemmaDatabase& lemmaDb);
};

} // namespace nlcolver
