#pragma once

#include "theory/arith/ArithSolverBase.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/nia/reasoners/UnivariateIntegerReasoner.h"
#include "theory/arith/nia/core/LinearNiaDomainReasoner.h"
#include "theory/arith/nia/reasoners/AlgebraicIntegerReasoner.h"
#include "theory/arith/nia/reasoners/SquareBoundReasoner.h"
#include "theory/arith/interval/IntervalEvaluator.h"
#include "theory/arith/nia/reasoners/SumOfSquaresBoundReasoner.h"
#include "theory/arith/nia/reasoners/BoundedNiaSolver.h"
#include "theory/arith/nia/reasoners/ProductPositivityReasoner.h"
#include "theory/arith/nia/reasoners/GcdDivisibilityReasoner.h"
#include "theory/arith/nia/search/NiaLocalSearch.h"
#include "theory/arith/bit_blast/BitBlastSolver.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/combination/SharedTermRegistry.h"
#include "theory/core/ActiveLiteralSet.h"
#include "expr/types.h"
#include <gmpxx.h>
#include <vector>
#include <memory>
#include <optional>
#include <unordered_set>
#include <deque>

namespace zolver {

class NiaLinearizationAdapter;
class CdcacCore;        // integer-aware CDCAC (libpoly-gated; constructed in .cpp)
class AlgebraBackend;

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
class NiaSolver : public ArithSolverBase {
public:
    explicit NiaSolver(std::unique_ptr<PolynomialKernel> kernel);
    ~NiaSolver();

    TheoryId id() const override { return TheoryId::NIA; }

    // NIA overrides assertLit: its admission policy uses an
    // ActiveLiteralSet for dedup and flags opposite-polarity as a
    // pending Unknown, neither of which the base default does. The
    // override still drives the shared `state_.trail`.
    // check() is the base default (runReasonerPipeline over the stages
    // registered in the constructor).
    void assertLit(const TheoryAtomRecord& atom, bool value,
                   int level, SatLit assertedLit) override;

    void setRegistry(TheoryAtomRegistry* reg);
    void setCoreIr(const CoreIr* ir) { coreIr_ = ir; }
    void setSharedTermRegistry(const SharedTermRegistry* reg) { sharedTermRegistry_ = reg; }

    bool supportsCombination() const override { return true; }

    TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;
    TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;

    std::vector<SharedEqualityPropagation>
    getDeducedSharedEqualities() override;

    std::optional<TheoryModel> getModel() const override;

protected:
    // Base rolls back state_.trail and clears its (unused-by-NIA)
    // pending slot; NIA syncs its polynomial constraint stack, active
    // literal set, its own level-tagged pendings, and interface
    // equalities here.
    void onBacktrack(int targetLevel) override;
    void onReset() override;

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
    ActiveLiteralSet activeSet_;
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
    bitblast::BitBlastSolver bitBlast_;
    ProductPositivityReasoner productPositivity_;
    GcdDivisibilityReasoner gcdDivisibility_;
    bool enableBitBlast_ = true;
    bool enableRefute_ = false;   // ZOLVER_NIA_REFUTE: bound-free product-positivity refutation
    bool enableBvDivMod_ = false; // ZOLVER_NIA_BV_DIVMOD: BV mod/div-by-2^k bit-extraction (BLAN-faithful)
    bool enableGcd_ = false;      // ZOLVER_NIA_GCD: multivariate GCD-divisibility refutation
    bool enableIcp_ = false;      // ZOLVER_NIA_ICP: interval contraction fixpoint (empty domain ⇒ UNSAT)
    bool enableCdcac_ = false;    // ZOLVER_NIA_CDCAC: integer-aware CDCAC (real-empty ⇒ int-UNSAT; integer-validated SAT)

    // Integer-aware CDCAC engine (Phase 4). Lazily constructed on first use and
    // only when libpoly is available; forward-declared to keep heavy NRA/libpoly
    // includes out of this header. Destroyed by the out-of-line ~NiaSolver().
    std::unique_ptr<AlgebraBackend> cdcacAlgebra_;
    std::unique_ptr<CdcacCore> cdcacCore_;

    std::optional<IntegerModel> currentModel_;

    // Phase 2: the normalized active constraints, produced by the
    // normalize stage and consumed by every downstream stage. Lives as a
    // member (rather than a check()-local) so the pipeline stages can be
    // separate units.
    std::vector<NormalizedNiaConstraint> normalized_;

    // Reasoner pipeline stages (Phase 2). Each returns nullopt to advance
    // to the next stage, or a verdict to stop. Registered as
    // CallbackReasoners in the constructor, in this order.
    std::optional<TheoryCheckResult> stagePending(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageNormalize(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stagePresolveFixpoint(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageTrivialConstants(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageDomainInference(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageSquareBound(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageSumOfSquares(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageUnivariate(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageAlgebraic(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageProductPositivity(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageGcdDivisibility(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageIcp(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageCdcac(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageBvDivMod(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageInterval(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageLinearization(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageBounded(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageBitBlast(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageLocalSearch(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stagePendingLemma(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageBranch(TheoryLemmaStorage&, TheoryEffort);

    const CoreIr* coreIr_ = nullptr;
    const SharedTermRegistry* sharedTermRegistry_ = nullptr;
    TheoryAtomRegistry* registry_ = nullptr;
    std::unique_ptr<NiaLinearizationAdapter> linAdapter_;
    std::deque<TheoryLemma> pendingLinLemmas_;

    struct InterfaceEq {
        SharedTermId a;
        SharedTermId b;
        SatLit reason;
        int level;
    };
    std::vector<InterfaceEq> interfaceEqualities_;
    std::vector<InterfaceEq> interfaceDisequalities_;

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
        TheoryLemmaStorage& lemmaDb);
};

} // namespace zolver
