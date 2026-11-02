#pragma once

#include "search/arith/ArithSolverBase.h"
#include "algebra/poly/PolynomialKernel.h"
#include "algebra/poly/PolynomialConverter.h"
#include "search/nia/preprocess/NiaNormalizer.h"
#include "search/nia/search/IntegerModelValidator.h"
#include "search/nia/core/DomainStore.h"
#include "search/nia/reasoners/UnivariateIntegerReasoner.h"
#include "search/nia/core/LinearNiaDomainReasoner.h"
#include "search/nia/reasoners/AlgebraicIntegerReasoner.h"
#include "search/nia/reasoners/SquareBoundReasoner.h"
#include "algebra/interval/IntervalEvaluator.h"
#include "search/nia/reasoners/SumOfSquaresBoundReasoner.h"
#include "search/nia/reasoners/BoundedNiaSolver.h"
#include "search/nia/reasoners/ProductPositivityReasoner.h"
#include "search/nia/reasoners/GcdDivisibilityReasoner.h"
#include "search/nia/reasoners/ModularResidueReasoner.h"
#include "search/nia/search/NiaLocalSearch.h"
#include "search/bitblast/BitBlastSolver.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/combination/SharedTermRegistry.h"
#include "contracts/ActiveLiteralSet.h"
#include "ir/types.h"
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
class NiaLinearDecider; // embedded bounded LIA model search (nia.linear-decide; own TU)
namespace farkas { struct FarkasProfile; struct FarkasOrContext; }

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
    // setNativeTerms override: stores via base + does NIA-specific Farkas-dump side
    // effect. setSharedTermRegistry uses the base implementation.
    void setNativeTerms(const NativeTerms* ir) override;

    bool supportsCombination() const override { return true; }

    TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;
    TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) override;

    std::vector<SharedEqualityPropagation>
    getDeducedSharedEqualities() override;

    // Look up the current NIA model value for a shared term so the combination
    // layer's model-based arrangement (TheoryManager.cpp §4) can see same-value
    // shared scalar pairs in array-combination mode (QF_ANIA / QF_AUFNIA).
    // Returns the literal value for shared constants and the currentModel_ /
    // lastValidatedFarkasModel_ entry for shared variables; nullopt otherwise.
    std::optional<RealValue> sharedTermArithValue(SharedTermId s) const override;

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
    // Sign-canonical key per polynomial for stagePolyConflict (group P and -P
    // together). A poly's canonical form is fixed, so this never invalidates;
    // computed once per distinct PolyId to bound neg() calls (kernel pool).
    std::unordered_map<PolyId, std::pair<std::string, bool>> polyCanonCache_;
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
    // Lazy cache: -1 unknown, 0 no array terms, 1 has array terms (Store/Select).
    // Set on first stageBitBlastEarly; reset by setNativeTerms. Gates bit-blast off on
    // array-combination problems (array-read results are EUF-managed shared terms;
    // bit-blasting the NIA constraints over them is wasteful + can mislead).
    mutable int bbArrayGate_ = -1;
    // Integer-aware CDCAC engine (Phase 4). Lazily constructed on first use and
    // only when libpoly is available; forward-declared to keep heavy NRA/libpoly
    // includes out of this header. Destroyed by the out-of-line ~NiaSolver().
    std::unique_ptr<AlgebraBackend> cdcacAlgebra_;
    std::unique_ptr<CdcacCore> cdcacCore_;

    // Embedded bounded LIA model search for the nia.linear-decide stage. In its own
    // TU (forward-declared) to keep LiaSolver/GeneralSimplex out of this header
    // to limit compilation dependencies. Lazily holds a LiaSolver sharing
    // NIA's TheoryAtomRegistry.
    // Destroyed by the out-of-line ~NiaSolver().
    std::unique_ptr<NiaLinearDecider> linDecider_;
    // Set of "proxy_name:truth" tokens we've already pinned via
    // registry->pinLiteral. Prevents the Farkas-Or stage's repeated
    // verdict-SAT path from re-issuing the same unit clauses on each
    // re-fire (those clauses are permanent in the SAT backend; emitting
    // duplicates is harmless but noisy).
    std::unordered_set<std::string> pinnedProxies_;
    // Count of consecutive Farkas-Or check passes that all confirmed
    // SAT but produced no new pin-lemma. After a small streak we bail
    // out with Unknown so the Solver.cpp Cap. 10 hook can recover the
    // theory-validated model directly.
    int farkasOrSatStreak_ = 0;

    std::optional<IntegerModel> currentModel_;
    // Survives reset()/backtrack — the last Farkas-Or candidate that the
    // validator confirmed against the ORIGINAL formula. Used by the
    // top-level Unknown fallback in Solver.cpp when the SAT engine times
    // out before its decision trail aligns with the theory's choice.
    // Sound: only ever supplements verdict via positively-validated model.
    std::optional<IntegerModel> lastValidatedFarkasModel_;

    // Phase 2: the normalized active constraints, produced by the
    // normalize stage and consumed by every downstream stage. Lives as a
    // member (rather than a check()-local) so the pipeline stages can be
    // separate units.
    std::vector<NormalizedNiaConstraint> normalized_;

    // Reasoner pipeline stages (Phase 2). Each returns nullopt to advance
    // to the next stage, or a verdict to stop. Registered as
    // CallbackReasoners in the constructor, in this order.
    std::optional<TheoryCheckResult> stagePending(TheoryLemmaStorage&, TheoryEffort);
    // Replay an all-linear active set into bounded integer search. Publish a
    // validated model or a root LP conflict; inconclusive search falls through.
    std::optional<TheoryCheckResult> stageLinearDecide(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageNormalize(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stagePresolveFixpoint(TheoryLemmaStorage&, TheoryEffort);
    // Append redundant
    // tightening cuts derived from single-variable bounds in normalized_.
    // Cuts are sound by construction so appending is sat/unsat preserving.
    std::optional<TheoryCheckResult> stageNlaCuts(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageTrivialConstants(TheoryLemmaStorage&, TheoryEffort);
    // Sound per-polynomial sign-consistency conflict. Every active constraint is
    // `P rel 0` — a constraint on the SIGN of P's value. Two constraints on the
    // SAME poly with contradictory signs (P<0 and P>0, or P=0 and P!=0) are
    // infeasible regardless of P's structure. The single-variable domain reasoner
    // misses this for multi-variable forms (it tracks variable domains, not the
    // value of a form like a-b), so in QF_UFNIA combination mode the loop branches
    // into finite-domain enumeration and stalls to unknown. Closes the
    // comparison-tautology class (Zohar AndOrXor/int_check). Runs before the
    // domain/finite-domain stages.
    std::optional<TheoryCheckResult> stageSignRefute(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stagePolyConflict(TheoryLemmaStorage&, TheoryEffort);
    // Sound difference-logic negative-cycle conflict, generalizing poly-conflict
    // from same-poly (2-var) to multi-variable difference chains. Active
    // constraints of the form `(i - j + k) rel 0` become difference edges; reuses
    // the project's BellmanFord/DifferenceGraph engine (theory/arith/dl) to detect
    // a negative cycle, whose edge-reason literals form the Farkas conflict.
    // Catches `r>t ∧ t>=s ∧ r<=s`-style 3+-variable conflicts that QF_NIA refutes
    // but QF_UFNIA combination misses (single-variable domain reasoning). Capped
    // at a small node count so the engine stays cheap on big problems.
    std::optional<TheoryCheckResult> stageDifferenceConflict(TheoryLemmaStorage&, TheoryEffort);
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
    // Partial/full-effort bit-blast. The backend validates SAT candidates;
    // conflicts require complete domain coverage.
    std::optional<TheoryCheckResult> stageBitBlastEarly(TheoryLemmaStorage&, TheoryEffort);
    // Full-effort candidate search for finite-lower-bound integer domains.
    // Widen each missing upper bound by 2^k - 1, enumerate integer/Boolean
    // assignments within the budget, and validate against the original formula.
    // Exhausting a bounded search never establishes unrestricted UNSAT.
    std::optional<TheoryCheckResult> stageEscalatingBounded(TheoryLemmaStorage&, TheoryEffort);
    // Farkas-Or model constructor stage (user 2026-06-02). For
    // disjunctive Farkas-certificate-synthesis problems (VeryMax/Stroeder).
    // Returns SAT only after validating
    // against the original NativeTerms formula; never UNSAT.
    std::optional<TheoryCheckResult> stageFarkasOr(
        TheoryLemmaStorage&, TheoryEffort, farkas::FarkasOrContext&);
    // Bounded-B real-relaxation refutation.
    // For each integer tuple of the bounded template vars B and
    // each Or-branch combo, substitute B and decide the REAL relaxation over
    // (lambda>=0, CT, residual) with CdcacCore. Every (B,combo) leaf
    // real-infeasible ⇒ sound integer UNSAT (ℤⁿ⊆ℝⁿ, exhaustive over the finite
    // B domain). Cracks Farkas-Or UNSAT cases (VeryMax/Stroeder) whose real
    // relaxation is feasible only at FRACTIONAL B. UNSAT is emitted only when
    // every leaf is a CdcacCore projection-certified Unsat; any Sat/Unknown
    // leaf (or any modelling gap) bails to nullopt.
    std::optional<TheoryCheckResult> tryBoundedBRefutation(
        const farkas::FarkasProfile& profile, bool& notRefutable);
    std::optional<TheoryCheckResult> stageLocalSearch(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stagePendingLemma(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageBranch(TheoryLemmaStorage&, TheoryEffort);

    // nativeTerms_, sharedTermRegistry_, sharedTermToVarName_, getVarNameForSharedTerm
    // now live in ArithSolverBase (hoisted 2026-06-04; was duplicated 4x).
    TheoryAtomRegistry* registry_ = nullptr;
    std::unique_ptr<NiaLinearizationAdapter> linAdapter_;
    std::deque<TheoryLemma> pendingLinLemmas_;

    struct InterfaceEq {
        SharedTermId a;
        SharedTermId b;
        SatLit reason;
        int level;
        // Converted (a - b) constraint, cached so
        // stageNormalize can merge interface (dis)equalities into the solve
        // WITHOUT placing them on the fragile active_/trail_ back-pop stack.
        PolyId diff = NullPoly;
        Relation rel = Relation::Eq;
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

} // namespace xolver
