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
#include "theory/arith/nia/SquareBoundReasoner.h"
#include "theory/arith/interval/IntervalEvaluator.h"
#include "theory/arith/nia/SumOfSquaresBoundReasoner.h"
#include "theory/arith/nia/BoundedNiaSolver.h"
#include "theory/arith/nia/NiaLocalSearch.h"
#include "theory/TheoryAtomRegistry.h"
#include "expr/types.h"
#include <gmpxx.h>
#include <vector>
#include <memory>
#include <optional>
#include <unordered_set>
#include <deque>

namespace nlcolver {

class NiaLinearizationAdapter;

/**
 * NIA (Nonlinear Integer Arithmetic) theory solver.
 *
 * NIA-Core pipeline:
 *   1. Normalize active constraints (clear denominators, strict → non-strict)
 *   2. Trivial constant handling
 *   3. Linear domain inference
 *   4. Square bound reasoning (x^2 <= c, x^2 = c, x^2 != c)
 *   5. Univariate reasoning (RRT roots)
 *   6. Algebraic reasoning (square, GCD, factor, modular)
 *   7. Empty domain check
 *   8. Bounded complete solver (enumeration / B&B)
 *   9. Local search heuristic
 *  10. Branch split lemma or Unknown
 */
class NiaSolver : public TheorySolver {
public:
    explicit NiaSolver(std::unique_ptr<PolynomialKernel> kernel);
    ~NiaSolver();

    TheoryId id() const override { return TheoryId::NIA; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value,
                   int level, SatLit assertedLit) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb) override;
    void reset() override;

    void setRegistry(TheoryAtomRegistry* reg);

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

    struct ActiveAssignment {
        int level;
        SatLit lit;
        TheoryAtomRecord atom;
        bool value;
    };

    std::unique_ptr<PolynomialKernel> kernel_;
    std::unique_ptr<PolynomialConverter> converter_;

    std::vector<ActiveNiaConstraint> active_;
    std::vector<NiaTrailEntry> trail_;
    std::vector<ActiveAssignment> activeAssignments_;
    std::optional<PendingConflict> pendingConflict_;
    std::optional<PendingUnknown> pendingUnknown_;

    // NIA-Core engines
    NiaNormalizer normalizer_;
    IntegerModelValidator validator_;
    DomainStore domains_;
    UnivariateIntegerReasoner univariate_;
    LinearNiaDomainReasoner linearDomain_;
    SquareBoundReasoner squareBound_;
    SumOfSquaresBoundReasoner sumOfSquaresBound_;
    IntervalEvaluator intervalEvaluator_;
    AlgebraicIntegerReasoner algebraic_;
    BoundedNiaSolver bounded_;
    NiaLocalSearch localSearch_;

    std::optional<IntegerModel> currentModel_;

    TheoryAtomRegistry* registry_ = nullptr;
    std::unique_ptr<NiaLinearizationAdapter> linAdapter_;
    std::deque<TheoryLemma> pendingLinLemmas_;

    struct BranchSplitKey {
        std::string var;
        mpz_class k;
        bool operator==(const BranchSplitKey& o) const {
            return var == o.var && k == o.k;
        }
    };
    struct BranchSplitKeyHash {
        std::size_t operator()(const BranchSplitKey& key) const {
            std::size_t h1 = std::hash<std::string>{}(key.var);
            std::size_t h2 = std::hash<std::string>{}(key.k.get_str());
            return h1 ^ (h2 + 0x9e3779b9 + (h1 << 6) + (h1 >> 2));
        }
    };
    std::unordered_set<BranchSplitKey, BranchSplitKeyHash> emittedSplits_;
    std::unordered_map<std::string, int> branchCountPerVar_;
    static constexpr int MAX_SINGLE_BOUND_SPLITS = 3;
    static constexpr int MAX_UNBOUNDED_SPLITS = 1;

    bool relationSatisfied(const mpq_class& val, Relation rel) const;
    std::optional<TheoryLemma> buildBranchLemma(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const DomainStore& domains,
        TheoryLemmaDatabase& lemmaDb);
};

} // namespace nlcolver
