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
#include "theory/arith/nia/reasoners/ModularResidueReasoner.h"
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

namespace xolver {

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
    ModularResidueReasoner modularResidue_;
    bool enableBitBlast_ = true;
    bool enableModular_ = true;   // constant-pow2-modulus residue refutation (L3) (promoted default-ON)
    bool enableRefute_ = true;    // bound-free product-positivity refutation (promoted default-ON)
    bool enableGcd_ = true;       // multivariate GCD-divisibility refutation (promoted default-ON)
    bool enableIcp_ = true;       // interval contraction fixpoint (empty domain ⇒ UNSAT) (promoted default-ON)
    bool enableCdcac_ = false;    // XOLVER_NIA_CDCAC: integer-aware CDCAC (real-empty ⇒ int-UNSAT; integer-validated SAT)
    bool normCache_ = true;       // incremental per-constraint normalize cache (kept in lockstep with active_) (promoted default-ON)

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
    // Stage 3 Phase C-3 (XOLVER_NIA_NLA_CUTS, default-OFF). Append redundant
    // tightening cuts derived from single-variable bounds in normalized_.
    // Cuts are sound by construction so appending is sat/unsat preserving.
    std::optional<TheoryCheckResult> stageNlaCuts(TheoryLemmaStorage&, TheoryEffort);
    // Stage 3 Phase 3b (XOLVER_NIA_BOUNDED_PARTIAL_EARLY, default-OFF).
    // Run partial bounded enumeration (BoundedNiaSolver::solvePartial)
    // RIGHT AFTER normalize, BEFORE every heavy per-prop stage. Solves
    // the same per-propagation budget exhaustion that motivated Phase 3a:
    // on ANIA/AUFNIA / SAT14-class inputs the budget is gone by the time
    // the late nia.bounded stage fires. Sound SAT-finding only; never
    // claims UNSAT.
    std::optional<TheoryCheckResult> stageBoundedEarly(TheoryLemmaStorage&, TheoryEffort);
    // SAT14-attack early-pipeline LocalSearch (XOLVER_NIA_LS_EARLY,
    // default-OFF). Same algorithmic stack as nia.local-search (twoLevel
    // + warm-start + multi-scale + quad-critical + fs-jump if those flags
    // are on) but fires RIGHT AFTER normalize, sharing CPU with the
    // upstream workhorses instead of starving at the end of the Full-
    // effort pipeline. The L1 sequence measurement showed LS has the
    // algorithmic reach to find SAT14 models (z3-extracted models are
    // small/moderate integers within multi-scale + fs-jump's coverage);
    // what's missing is the budget to RUN the search. Per-call budget
    // capped via XOLVER_NIA_LS_EARLY_BUDGET_MS (default 200), cumulative
    // via XOLVER_NIA_LS_EARLY_TOTAL_MS (default 5000). Sound SAT-finder
    // only — verdicts always validator-gated.
    std::optional<TheoryCheckResult> stageLocalSearchEarly(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageTrivialConstants(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageDomainInference(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageSquareBound(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageSumOfSquares(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageUnivariate(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageAlgebraic(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageProductPositivity(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageGcdDivisibility(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageModular(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageIcp(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageCdcac(TheoryLemmaStorage&, TheoryEffort);
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
        // XOLVER_NIA_IFACE_LIFECYCLE: the converted (a - b) constraint, cached so
        // stageNormalize can merge interface (dis)equalities into the solve
        // WITHOUT placing them on the fragile active_/trail_ back-pop stack.
        PolyId diff = NullPoly;
        Relation rel = Relation::Eq;
    };
    std::vector<InterfaceEq> interfaceEqualities_;
    std::vector<InterfaceEq> interfaceDisequalities_;

    // XOLVER_NIA_IFACE_LIFECYCLE (read once in ctor): when set, Nelson-Oppen
    // interface (dis)equalities are kept out of active_/trail_/activeSet_ and
    // are instead merged into the constraint set at stageNormalize, with a
    // level-correct remove_if backtrack and a full clear on a level-0 reset.
    // Fixes the false "opposite polarity" Unknown that aborted QF_UFNIA/QF_ANIA
    // model checks: interface eqs asserted during check() (after the ascending
    // re-assert loop) made trail_ non-monotonic, so onBacktrack's back-pop left
    // stale entries that polluted activeSet_ via rebuildFromActive, and level-0
    // interface eqs accumulated across the many Full-effort model checks.
    bool ifaceLifecycleEnabled_ = false;

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

} // namespace xolver
