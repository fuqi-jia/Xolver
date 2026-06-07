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
#include "theory/arith/nia/reasoners/GroebnerIdealReasoner.h"
#include "theory/arith/nia/reasoners/ModEqConstFact.h"
#include "theory/arith/nia/reasoners/ModEqConstReasoner.h"
#include "theory/arith/nia/reasoners/DioReasoner.h"
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
namespace farkas { struct FarkasProfile; }  // bounded-B refutation input

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
    // setCoreIr override: stores via base + does NIA-specific Farkas-dump side
    // effect. setSharedTermRegistry uses the base implementation.
    void setCoreIr(const CoreIr* ir) override;

    // Track A Phase 1.3: receive ModEqConstFacts captured by IntDivModLowerer.
    // Called by Solver::Impl after preprocessing and theory-solver setup. The
    // facts are consumed by stageNativeModEqConst on each NIA check call.
    void setModEqConstFacts(ModEqConstFactList facts);

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
    // Gated by XOLVER_NIA_SHARED_ARITH_VALUE (default-ON) so the historical
    // "NIA returns nullopt -> arrangement skipped" behaviour can be restored
    // if the arrangement loop turns out to oscillate on QF_(AUF)NIA.
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
    GroebnerIdealReasoner groebner_;
    // Track A Phase 1.3 — native (mod x y) = c reasoner. Receives the fact
    // list from IntDivModLowerer (via setModEqConstFacts) and runs rules 1-3
    // at each Standard-effort check.
    ModEqConstFactList modEqConstFacts_;
    ModEqConstReasoner modEqConst_;
    // Symbolic modular Diophantine refutation (nia.dio); congruences built from
    // modEqConstFacts_ ((mod x m)=c => x≡c mod m).
    DioReasoner dio_;
    bool enableBitBlast_ = true;
    // Lazy cache: -1 unknown, 0 no array terms, 1 has array terms (Store/Select).
    // Set on first stageBitBlastEarly; reset by setCoreIr. Gates bit-blast off on
    // array-combination problems (array-read results are EUF-managed shared terms;
    // bit-blasting the NIA constraints over them is wasteful + can mislead).
    mutable int bbArrayGate_ = -1;
    // bit-blast-early dedup: bit-blast-early re-blasts the WHOLE free problem on
    // every Standard-effort cb_propagate. The free problem is fixed across calls
    // with the same active-constraint set, so an UNKNOWN result repeats — yet on
    // large encodings each blast costs seconds (00314 80x/11s, a UFDTNIA 4x/14.6s)
    // and dominates the budget. Record the normalized_.size() at which the last
    // blast returned UNKNOWN and skip re-blasting at that same size. Sound:
    // bit-blast-early is a Standard-effort, candidate-only heuristic; skipping it
    // only forgoes an early SAT that the Full-effort nia.bit-blast (and SAT
    // search) still find. SIZE_MAX = no cached unknown.
    mutable size_t bbEarlyUnkSize_ = static_cast<size_t>(-1);
    bool enableModular_ = true;   // constant-pow2-modulus residue refutation (L3) (promoted default-ON)
    bool enableGroebner_ = false; // XOLVER_NIA_GROBNER: ideal saturation (1∈ideal ⇒ UNSAT) — default-OFF (iter-77 cherry-pick from 7afeda9)
    // L4.1 — modular reasoner warm-start memoization. When the active
    // normalized_ stream's signature matches modularLastSignature_ AND
    // the last run was NoChange, stageModular skips re-running the
    // detection + Hensel + chain composition + residue enumeration and
    // returns NoChange immediately. Sound: a NoChange replay under
    // unchanged signature writes no state and emits no verdict. On
    // backtrack / reset the cache is invalidated.
    uint64_t modularLastSignature_ = 0;
    bool modularLastWasNoChange_ = false;
    bool modularSignatureValid_ = false;
    // Phase D (master 2026-06-01) — per-cb_propagate dispatch cache
    // (XOLVER_NIA_DISPATCH_CACHE, default-OFF). When TheoryManager calls
    // check() repeatedly without any new asserted literal (typical at
    // Full-effort re-drive and in N-O exchange for combined logics), the
    // 16-stage pipeline re-runs over identical state. Cache the active_
    // signature at the END of the most recent "would have been
    // consistent" pipeline run; on the next call, if the signature
    // matches, return consistent immediately. assertLit, onBacktrack,
    // and onReset all invalidate. Sound: any consistent verdict was
    // already validated by the full pipeline once at this signature.
    uint64_t dispatchCacheSignature_ = 0;
    bool dispatchCacheValid_ = false;
    // HYB-1 partition DIAG: print once per solve (reset by onReset).
    bool partitionDiagPrinted_ = false;
    bool enableRefute_ = true;    // bound-free product-positivity refutation (promoted default-ON)
    bool enableGcd_ = true;       // multivariate GCD-divisibility refutation (promoted default-ON)
    bool enableIcp_ = true;       // interval contraction fixpoint (empty domain ⇒ UNSAT) (promoted default-ON)
    bool enableCdcac_ = false;    // XOLVER_NIA_CDCAC: integer-aware CDCAC (real-empty ⇒ int-UNSAT; integer-validated SAT)
    bool normCache_ = true;       // incremental per-constraint normalize cache (kept in lockstep with active_) (promoted default-ON)
    // (iter-77 cherry-pick of 7afeda9 added groebner_ field + enableGroebner_ above)

    // Integer-aware CDCAC engine (Phase 4). Lazily constructed on first use and
    // only when libpoly is available; forward-declared to keep heavy NRA/libpoly
    // includes out of this header. Destroyed by the out-of-line ~NiaSolver().
    std::unique_ptr<AlgebraBackend> cdcacAlgebra_;
    std::unique_ptr<CdcacCore> cdcacCore_;

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
    // Reference NLSAT-plan §2.3 + §5.1 step 1: when every currently-active
    // atom has a polynomial of total degree ≤ 1, NIA's verdict on this
    // active set is definitionally equal to LIA's. LIA is registered
    // alongside NIA by TheoryFactory and will own the check in the same
    // CDCL(T) round. This stage short-circuits the 19-stage NIA pipeline
    // for those cb_propagate calls. Sound: returning Consistent here is
    // equivalent to "no nonlinear obligation"; LIA's verdict is then the
    // final NIA verdict.
    std::optional<TheoryCheckResult> stagePureLinearShortcut(TheoryLemmaStorage&, TheoryEffort);
    // Phase D — dispatch cache front stage. Compares current active_
    // signature against dispatchCacheSignature_; returns consistent()
    // on hit, nullopt on miss. Default-OFF flag XOLVER_NIA_DISPATCH_CACHE.
    std::optional<TheoryCheckResult> stageDispatchCacheLookup(TheoryLemmaStorage&, TheoryEffort);
    // Phase D — dispatch cache tail stage (RIGHT BEFORE stageBranch).
    // If we reach it, all earlier stages returned nullopt, so the
    // base will fall through to consistent(). Record the active_
    // signature so the next identical call short-circuits.
    std::optional<TheoryCheckResult> stageDispatchCacheRecord(TheoryLemmaStorage&, TheoryEffort);
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
    // Sound per-polynomial sign-consistency conflict. Every active constraint is
    // `P rel 0` — a constraint on the SIGN of P's value. Two constraints on the
    // SAME poly with contradictory signs (P<0 and P>0, or P=0 and P!=0) are
    // infeasible regardless of P's structure. The single-variable domain reasoner
    // misses this for multi-variable forms (it tracks variable domains, not the
    // value of a form like a-b), so in QF_UFNIA combination mode the loop branches
    // into finite-domain enumeration and stalls to unknown. Closes the
    // comparison-tautology class (Zohar AndOrXor/int_check). Runs before the
    // domain/finite-domain stages.
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
    std::optional<TheoryCheckResult> stageGroebner(TheoryLemmaStorage&, TheoryEffort);
    // Track A Phase 1.3 — native ModEqConst rules 1-3. Only fires when the
    // XOLVER_NIA_NATIVE_MODEQCONST flag is set AND the fact list is non-empty.
    std::optional<TheoryCheckResult> stageNativeModEqConst(TheoryLemmaStorage&, TheoryEffort);
    // Symbolic modular Diophantine refutation (XOLVER_NIA_DIO). Builds DioCongruences
    // from active (mod x m)=c facts and runs DioReasoner over normalized_.
    std::optional<TheoryCheckResult> stageDio(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageIcp(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageCdcac(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageInterval(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageLinearization(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageBounded(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageBitBlast(TheoryLemmaStorage&, TheoryEffort);
    // H3 (master 2026-06-01) — bit-blast EARLY stage. Same algorithm as
    // stageBitBlast but registered Standard+Full so it fires at Standard
    // effort on inputs (SAT14 class) where the SAT layer never reaches a
    // complete assignment within budget (Full-effort never triggers).
    // Mirrors the stageLocalSearchEarly pattern. Default-OFF flag
    // XOLVER_NIA_BB_EARLY. Sound: bit-blast is candidate-only — every Sat
    // model is validated against the original constraints (invariant 1).
    std::optional<TheoryCheckResult> stageBitBlastEarly(TheoryLemmaStorage&, TheoryEffort);
    // HYB-3 (master 2026-06-02). For SAT14-style partition (|B| small,
    // |U| large), iterate K random samples of the bounded vars within
    // their boxes; for each, run a tight-budget LS on the unbounded
    // vars and validate any SAT candidate. Sound: every returned Sat
    // is IntegerModelValidator-gated against the original constraint
    // set. Default-OFF flag XOLVER_NIA_HYB_BB_LS. Full-effort only —
    // the heavy LS-probe loop should not run per Standard cb_propagate.
    std::optional<TheoryCheckResult> stageHybridBbLs(TheoryLemmaStorage&, TheoryEffort);
    // LBBB Phase 2 (master 2026-06-02). LS-Bounded Bit-Blast Fallback.
    // After local-search exits without finding SAT (its `hasFailed()`
    // flag is true), bit-blast the formula over the BOX that LS
    // explored, extended by a buffer. The BV solve uses the existing
    // BitBlastSolver with a custom DomainStore restricted to the
    // LS-visited box, then validates any Sat candidate against the
    // ORIGINAL NIA constraints. Default-OFF (XOLVER_NIA_LBBB),
    // Full-effort only.
    std::optional<TheoryCheckResult> stageBoundedBitBlast(TheoryLemmaStorage&, TheoryEffort);
    // Escalating-bounded SAT-finder for the unbounded-≥0 NIA pattern (AProVE
    // class, ~4,571 cases per master). When some variable has a finite lower
    // bound but no upper bound, BoundedNiaSolver bails to UnknownUnsupported
    // and downstream stages (bit-blast, modular, LS) may also miss the case.
    // This stage augments domains_ in a SCRATCH copy by adding upper bounds
    // `lower + 2^k - 1` for each unbounded-low var, then calls bounded_.solve
    // on the augmented store, escalating k each iteration. SAT in any
    // augmented box is also SAT in the original (smaller domain ⊆ original
    // domain), and bounded_.solve validates every candidate via validator_
    // against the original constraints — sound by invariant 1. The escalation
    // terminates structurally when ENUMERATION_THRESHOLD bites
    // (UnknownBudget) on the augmented box, never via an artificial k cap.
    // Default-ON since iter#11 (2026-06-05) — promoted after 100-AProVE
    // sample showed +1 recovery on baseline-stuck cases with 0 regressions
    // (12 buckets, 670 reg cases all 0-unsound), and the iter#10 AMV
    // ConstInt-string fix made every validator verdict precise. Opt out via
    // XOLVER_NIA_BOUNDED_ESCALATE=0. Full-effort only.
    std::optional<TheoryCheckResult> stageEscalatingBounded(TheoryLemmaStorage&, TheoryEffort);
    // HYB-2 (master 2026-06-02, post-Smart-LS). Coordinated LS-on-U +
    // BB-on-B for partition profiles where B dominates (|B| > |U|;
    // ITS-like, H5 finding). LS-tracked bounds give per-U-var
    // midpoints; pin U vars at midpoint via DomainStore singletons;
    // run BitBlastSolver on the residual formula (which is now bounded
    // since the unbounded U vars are pinned). Validate any Sat candidate
    // against the ORIGINAL constraints. Default-OFF XOLVER_NIA_HYB_LS_BB,
    // Full-effort only.
    std::optional<TheoryCheckResult> stageHybridLsBb(TheoryLemmaStorage&, TheoryEffort);
    // Farkas-Or model constructor stage (user 2026-06-02). For
    // disjunctive Farkas-certificate-synthesis problems (VeryMax/Stroeder).
    // Default-OFF XOLVER_NIA_FARKAS_OR. Returns SAT only after validating
    // against the original CoreIr formula; never UNSAT.
    std::optional<TheoryCheckResult> stageFarkasOr(TheoryLemmaStorage&, TheoryEffort);
    // Bounded-B real-relaxation refutation (XOLVER_NIA_FARKAS_BOUNDED_REFUTE,
    // default-OFF). For each integer tuple of the bounded template vars B and
    // each Or-branch combo, substitute B and decide the REAL relaxation over
    // (lambda>=0, CT, residual) with CdcacCore. Every (B,combo) leaf
    // real-infeasible ⇒ sound integer UNSAT (ℤⁿ⊆ℝⁿ, exhaustive over the finite
    // B domain). Cracks Farkas-Or UNSAT cases (VeryMax/Stroeder) whose real
    // relaxation is feasible only at FRACTIONAL B. UNSAT is emitted only when
    // every leaf is a CdcacCore projection-certified Unsat; any Sat/Unknown
    // leaf (or any modelling gap) bails to nullopt.
    std::optional<TheoryCheckResult> tryBoundedBRefutation(
        const farkas::FarkasProfile& profile);
    std::optional<TheoryCheckResult> stageLocalSearch(TheoryLemmaStorage&, TheoryEffort);
    // LS-SMART-Z5 (master 2026-06-02): Boolean-extend re-validate.
    // When stageLocalSearch's cost==0 gate fails, LS may still have visited a
    // lowest-cost candidate (lsContext_.bestAssignment) that violates some
    // active atom but satisfies the FULL original-formula because the violated
    // atom appears in a disjunctive context whose other disjunct is true under
    // the candidate. Walk the ORIGINAL coreIr_ assertions via ArithModelValidator
    // and return Sat if Satisfied. Sound: ArithModelValidator is exact, the
    // same validator used by Solver::Impl at the top-level soundness gate.
    // Default-OFF XOLVER_NIA_LS_BOOL_EXTEND, Full-effort only.
    std::optional<TheoryCheckResult> stageLocalSearchBoolExtend(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stagePendingLemma(TheoryLemmaStorage&, TheoryEffort);
    std::optional<TheoryCheckResult> stageBranch(TheoryLemmaStorage&, TheoryEffort);

    // coreIr_, sharedTermRegistry_, sharedTermToVarName_, getVarNameForSharedTerm
    // now live in ArithSolverBase (hoisted 2026-06-04; was duplicated 4x).
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

    // XOLVER_NIA_IFACE_LIFECYCLE (default-ON since 2026-06-02 COMB-1 audit):
    // Nelson-Oppen interface (dis)equalities are kept out of active_/trail_/
    // activeSet_ and instead merged into the constraint set at stageNormalize,
    // with a level-correct remove_if backtrack and a full clear on a level-0
    // reset. Fixes the false "opposite polarity" Unknown that aborted
    // QF_UFNIA/QF_ANIA model checks: interface eqs asserted during check()
    // (after the ascending re-assert loop) made trail_ non-monotonic, so
    // onBacktrack's back-pop left stale entries that polluted activeSet_ via
    // rebuildFromActive, and level-0 interface eqs accumulated across the many
    // Full-effort model checks. Verified 0 unsound on 191 cases (100 uniform
    // QF_UFNIA + 91 Zohar) with +recovery direction. A/B escape:
    // XOLVER_NIA_IFACE_LIFECYCLE=0 disables.
    bool ifaceLifecycleEnabled_ = true;

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
