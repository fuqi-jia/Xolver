#pragma once
// Auto-extracted declaration of Solver::Impl (was an inline class in
// Solver.cpp). The larger method bodies live out-of-line in the
// Solver_impl_*.cpp translation units; smaller / #ifdef-guarded methods
// stay inline here. Member state is verbatim. Behavior is unchanged.
#include "xolver/Solver.h"
#include "xolver/Result.h"
#include "expr/ir.h"
#include "expr/CoreIteLowerer.h"
#include "frontend/preprocess/ArithCastNormalizer.h"
#include "frontend/preprocess/BoolSubtermPurifier.h"
#include "frontend/preprocess/UfInArithPurifier.h"
#include "frontend/preprocess/RealDivLowerer.h"
#include "frontend/preprocess/ToIntDefinitionalLowerer.h"
#include "frontend/preprocess/IntDivModConstantFold.h"
#include "frontend/preprocess/StoreTowerEqMultiset.h"
#include "frontend/preprocess/ArrayReadOverWrite.h"
#include "frontend/preprocess/targeted/ReadOnlyArrayElim.h"
#include "frontend/preprocess/targeted/UfApplyAckermann.h"
#include "frontend/preprocess/IntDivModLowerer.h"
#include "theory/arith/logics/nia/reasoners/ModEqConstFact.h"
#include "frontend/preprocess/ZoharBwiAxiomEmitter.h"
#include "frontend/preprocess/ModularConsistencyChecker.h"
#include "frontend/preprocess/NaryDistinctLowerer.h"
#include "frontend/preprocess/ToRealLiteralFold.h"
#include "frontend/preprocess/UnconditionalConstantPropagation.h"
#include "frontend/preprocess/FormulaRewriter.h"
#include "frontend/preprocess/MonomialSharingPass.h"
#include "frontend/preprocess/SolveEqs.h"
#include "frontend/preprocess/ModelConverter.h"
#include "frontend/preprocess/UnconstrainedElim.h"
#include "frontend/factory/StrategyPresets.h"
#include <cstdlib>
#include <csignal>
#include <csetjmp>
#include "theory/arith/kernel/search/CandidateModelSearch.h"
#include "proof/ArithModelValidator.h"
#include <gmpxx.h>
#include "expr/Smt2Dumper.h"
#include "parser/adapter.h"
#include "sat/SatSolver.h"
#include "frontend/atomization/Atomizer.h"
#include "theory/arith/logics/nia/farkas/FarkasOrDetector.h"
#include "theory/core/TheoryManager.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "frontend/factory/TheoryFactory.h"
#include "theory/core/LogicFeatureDetector.h"
#include "theory/arith/kernel/bit_blast/EagerBitBlastSolver.h"
#ifdef XOLVER_ENABLE_CASESTATS
#ifdef XOLVER_ENABLE_CASESTATS
#include "util/CaseStats.h"
#endif
#endif
#include "util/EnvParam.h"
#include "util/SolveClock.h"

#include "sat/CadicalBackend.h"
#include "sat/CadicalTheoryPropagator.h"
#include "sat/RelevancyEngine.h"

#include <somtparser/frontend/parser.h>

#include <iostream>
#include <sstream>
#include <set>
#include <unordered_map>
#include <map>
#include <functional>
#include <optional>
#include <chrono>
#include <thread>
#include <atomic>

namespace xolver {
class Solver::Impl {
public:
    std::string logic = "ALL";
    std::unordered_map<std::string, OptionValue> options;

    std::unique_ptr<SOMTParser::Parser> parser;
    std::unique_ptr<CoreIr> ir;
    std::unique_ptr<SatSolver> sat;
    SortId boolSortId_ = NullSort;
    SortId intSortId_ = NullSort;
    SortId realSortId_ = NullSort;
    std::unique_ptr<SharedTermRegistry> sharedTermRegistry_;
    std::optional<TheorySolver::TheoryModel> lastModel_;
    std::vector<Term> lastAssumptions_;
    // Assumption-based unsat-core (checkSatAssuming). assumptionRoots_ holds the
    // ExprIds of the in-flight assumptions; EMPTY for a plain checkSat, in which
    // case the core machinery in checkSatInternal is fully inert and the default
    // path is byte-identical. lastUnsatCore_ holds the minimized subset that
    // CaDiCaL's failed() reported as necessary for UNSAT (consumed by
    // getUnsatCore()); seeded to the full assumption set as a sound fallback.
    std::vector<ExprId> assumptionRoots_;
    std::vector<Term> lastUnsatCore_;
    // File-level unsat-core (:produce-unsat-cores / setOption "produce-unsat-cores").
    // When set, checkSatInternal gates every top-level assertion A with a fresh
    // boolean indicator (A becomes (=> a A)) and assumes all indicators, so
    // failed() pinpoints which ORIGINAL assertions form the core. indicatorRoots_
    // are the indicator vars (the literals to assume); indicatorCoreTerms_[k] is
    // the ORIGINAL assertion Term reported when indicator k fails. Default OFF →
    // the whole mechanism is inert and the solve path is byte-identical.
    bool produceUnsatCores_ = false;
    std::vector<ExprId> indicatorRoots_;
    std::vector<Term> indicatorCoreTerms_;
    // Original (pre-lowering) assertion roots, snapshotted each checkSat for
    // the independent model self-check (modelMatchesOriginal).
    std::vector<ExprId> originalAssertions_;
    // Path of the file this problem was parsed from, retained so the portfolio
    // executor (XOLVER_STRAT_PORTFOLIO) can re-establish PRISTINE state per arm
    // via reset()+parseFile. Cleared by a programmatic assertFormula (which
    // would be lost on re-parse), which forces the executor to single-arm.
    std::string sourcePath_;
    // The CaDiCaL backend of the in-flight checkSatInternal, published so the
    // portfolio's per-arm budget watchdog can async-interrupt a running solve
    // (CaDiCaL terminate() is thread-safe). nullptr whenever no solve is live;
    // an RAII guard in checkSatInternal clears it on every exit path.
    std::atomic<CadicalBackend*> activeBackend_{nullptr};

    // Records variables eliminated by solve-eqs (XOLVER_PP_SOLVE_EQS) so their
    // values can be replayed onto the final model (↔SAT replay correctness).
    // Reset at the start of each checkSat's preprocessing; empty when the pass
    // did not run (flag off / incremental scope).
    ModelConverter modelConverter_;

    // Read records from ReadOnlyArrayElim (XOLVER_TARGETED_PP). Each says a
    // scalar array read `(select arrOperand idxExpr)` was Ackermannized into a
    // fresh variable. Post-solve, the validator re-keys these as select
    // overrides so the ORIGINAL array-bearing assertions still evaluate (the
    // arrOperand/idxExpr ExprIds are hash-cons-stable in originalAssertions_).
    // Cleared each checkSat; empty when the pass did not fire.
    std::vector<ReadOnlyArrayElim::ReadRec> roaeReads_;
    // ReadOnlyArrayElim write-array mode (avg20/swap): free read-only array
    // Variable ExprIds the validator treats as free (any equality -> false), and
    // a flag that this relaxation fired — in which case UNSAT is suppressed to
    // Unknown (only the validator-confirmed SAT direction is sound).
    std::unordered_set<ExprId> roaeFreeArrayVars_;
    bool roaeUsedWriteArray_ = false;

    // Constants bound by UnconditionalConstantPropagation (Cap 8a). Captured
    // immediately after `cprop.commit()` so model emission and validators can
    // fill in user vars that UCP substituted away (the post-UCP IR has only
    // the source-of-binding equality at top-level; nested ones get folded to
    // `true`, leaving the var absent from downstream theories and therefore
    // absent from the printed model — defaults to 0, validator flags
    // false-SAT). Sound: every model of the original formula satisfies these
    // bindings by construction of UCP.
    std::unordered_map<std::string, mpq_class> fixedBindings_;

    // Partial-function (div/mod-by-zero) model support. divModOrigins_ is
    // captured from IntDivModLowerer; partialFuncModel_ is the chosen total
    // extension at undefined inputs, built from the final model (see
    // buildPartialFuncModel) and emitted as define-fun shadows in dumpModel.
    std::vector<DivModOrigin> divModOrigins_;
    // Track A Phase 1.3 — facts captured from IntDivModLowerer for the
    // native ModEqConstReasoner. Handed off to NiaSolver after setupSolvers.
    ModEqConstFactList modEqConstFacts_;
    struct PartialFuncModel {
        std::map<mpq_class, mpq_class> divZero;  // a -> chosen (div a 0)
        std::map<mpq_class, mpq_class> modZero;  // a -> chosen (mod a 0)
        bool inconsistent = false;   // same input -> two outputs (safety net)
        bool realDivByZero = false;  // a Real `/` had a 0 denominator (round-1 gate)
    };
    PartialFuncModel partialFuncModel_;

    std::string lastUnknownReason_;
    std::string lastUnknownCode_;
    std::string lastUnknownComponent_;
    std::string lastUnknownDetail_;

    // True iff the SMT-LIB input set :produce-models / issued (get-model).
    bool modelRequestedImpl() const;

    // Merge UCP fixedBindings_ into lastModel_'s string + numeric channels for
    // any var not already present. Called at every site that sets lastModel_
    // so validators (modelViolatesOriginal, combinationModelDefinitelyViolates,
    // arrayModelValidates) and emit (Solver::getModel, dumpModel) all see the
    // eliminated user vars at their UCP-bound constants instead of defaulting
    // to 0 and flagging a false-SAT.
    void mergeFixedBindings();

    // True only on a DEFINITE violation of an original (pre-lowering)
    // assertion by the current lastModel_ (mirrors the negation of
    // Solver::modelMatchesOriginal). Drives the validated model-repair.
    bool modelViolatesOriginal() const;

    // QF_AX: re-validate the extracted array model against the ORIGINAL
    // assertions. Returns true only if the model is present and the validator
    // does NOT report a definite violation. A missing model or an
    // Indeterminate result is treated as "cannot confirm" → false (gate to
    // Unknown), so we never emit an unvalidated array sat.
    bool arrayModelValidates() const;

    // Array SAT soundness safety net (ALL tracks, incl. Single-Query). Builds
    // the array model internally and runs ArithModelValidator over the ORIGINAL
    // assertions, returning true ONLY when the verdict is a DEFINITE Violated.
    // Unlike arrayModelValidates() this is conservative in the SOUND direction:
    //   - a missing model / empty interps / Indeterminate -> false (do NOT
    //     downgrade — never spuriously reject a genuine sat);
    //   - only a definite Violated -> true (downgrade Sat -> Unknown).
    // This guards against a missed Row2/Ext instance escaping as a spurious sat
    // even when no model was requested. It must never fire for a genuinely-sat
    // case (the recently-fixed model construction produces valid store/const
    // models that validate).
    bool arrayModelDefinitelyViolates() const;

    // UF-combination soundness floor (QF_UFLIA / QF_UFLRA proper, no array).
    // Mirrors arrayModelDefinitelyViolates but routes function interpretations
    // from the EUF Track-3 model so UF apps over arith args evaluate concretely
    // instead of returning Indeterminate. Returns true ONLY on a DEFINITE
    // Violated — Indeterminate / unknown stays sat (never spuriously reject a
    // genuine sat). Catches the Wisa-class false-SAT: arith picks fmt1 such
    // that select_format(fmt1) value matches percent locally, but EUF never
    // had to merge them, so the negated goal is "satisfied" only because the
    // joint model is inconsistent — the validator's funcInterp table resolves
    // it concretely and exposes the violation.
    bool combinationModelDefinitelyViolates() const;

    // STRICT model validation (XOLVER_PP_STRICT_VALIDATION). Returns true ONLY
    // when the extracted model POSITIVELY satisfies every original assertion
    // (Verdict::Satisfied). Unlike the *Violates helpers (which act only on a
    // DEFINITE violation), this is the trust gate: an unconfirmed model
    // (Indeterminate — missing assignment, uninterpreted function, construct the
    // validator cannot evaluate) is NOT accepted as sat. We populate declared
    // user variables with the same 0/false defaults dumpModel emits, so the
    // model checked here is exactly the one that would be printed.
    bool modelPositivelyValidates() const;

    // Build the partial-function (div/mod-by-zero) model from the final model.
    // For each lowered div/mod whose divisor is 0 under the model, record the
    // chosen result (the value of the fresh quotient q / remainder r) keyed by
    // the dividend value a. A FuncInterp is a function, so re-encountering the
    // same input with a different output signals a model-extraction bug
    // (partialFuncModel_.inconsistent). Also gates Real `/` by a 0 denominator,
    // which round 1 does not emit.
    void buildPartialFuncModel();

    // True iff some Real `/` in the original assertions has a 0 denominator
    // under the model (round-1 gate: such a model is downgraded to Unknown
    // because we do not yet emit a `define-fun /` shadow).
    bool realDivisionByZeroUnderModel(const ArithModelValidator& v) const;

    // True iff the ORIGINAL assertions syntactically contain a real `/`. The
    // realDivPurifySatFloor (which re-validates every nonlinear-real sat via the
    // RealValue ArithModelValidator) only guards the div-by-0 functional-consistency
    // corner of real division — with no real `/`, that corner cannot exist, so the
    // floor is pure overhead AND, for an algebraic (Q(sqrt c)) sat model, its
    // >=2-algebraic RealValue evaluation of a high-degree polynomial can blow up (the
    // Geogebra 17a/17b hang). Gating the floor on actual real division keeps the
    // soundness guard where it is needed and lets the algebraic-sat cascade through.
    // Memoized DAG walk.
    bool hasRealDivisionInOriginal() const;

#ifdef XOLVER_ENABLE_CASESTATS
    void parseUnknownReasonIntoStats() {
        // Derive structured unknown fields from the free-text reason.
        const std::string& r = lastUnknownReason_;
        if (r.empty()) return;

        // Component detection from prefix
        auto colonPos = r.find(':');
        std::string prefix = (colonPos != std::string::npos) ? r.substr(0, colonPos) : r;

        if (prefix == "IntDivModLowerer") {
            lastUnknownComponent_ = "IntDivModLowerer";
            lastUnknownCode_ = "FRONTEND_UNSUPPORTED_DIVMOD";
            caseStats_.failureStage = "frontend";
        } else if (prefix == "ToIntDefinitionalLowerer") {
            lastUnknownComponent_ = "ToIntDefinitionalLowerer";
            lastUnknownCode_ = "FRONTEND_UNSUPPORTED_TO_INT";
            caseStats_.failureStage = "frontend";
        } else if (prefix == "LogicFeatureDetector") {
            lastUnknownComponent_ = "LogicFeatureDetector";
            lastUnknownCode_ = "FRONTEND_UNSUPPORTED_FEATURE";
            caseStats_.failureStage = "frontend";
        } else if (prefix == "Atomizer") {
            lastUnknownComponent_ = "Atomizer";
            lastUnknownCode_ = "ATOMIZER_UNSUPPORTED";
            caseStats_.failureStage = "atomizer";
        } else if (prefix == "TheoryFactory") {
            lastUnknownComponent_ = "TheoryFactory";
            lastUnknownCode_ = "FRONTEND_LOGIC_MISMATCH";
            caseStats_.failureStage = "frontend";
        } else if (prefix == "SAT") {
            lastUnknownComponent_ = "SAT";
            lastUnknownCode_ = "SAT_ABORT";
            caseStats_.failureStage = "sat";
        } else if (prefix == "Theory") {
            lastUnknownComponent_ = "Theory";
            lastUnknownCode_ = "THEORY_UNKNOWN";
            caseStats_.failureStage = "theory";
        } else {
            lastUnknownComponent_ = "Unknown";
            lastUnknownCode_ = "UNKNOWN";
            caseStats_.failureStage = "unknown";
        }
        lastUnknownDetail_ = r;
    }

    void finalizeCaseStats(Result result, double timeMs,
                           const CadicalTheoryPropagator* propagator = nullptr,
                           const TheoryManager* theoryManager = nullptr,
                           const CadicalBackend* cadicalBackend = nullptr,
                           const Atomizer* atomizer = nullptr,
                           const TheoryAtomRegistry* registry = nullptr) {
        caseStats_.timeMs = timeMs;
        caseStats_.result = (result == Result::Sat) ? "sat" :
                            (result == Result::Unsat) ? "unsat" :
                            (result == Result::Unknown) ? "unknown" : "error";
        if (result == Result::Unknown) {
            parseUnknownReasonIntoStats();
            caseStats_.unknownCode = lastUnknownCode_;
            caseStats_.unknownComponent = lastUnknownComponent_;
            caseStats_.unknownDetail = lastUnknownDetail_;
        }
        if (theoryManager) {
            caseStats_.activeTheories = theoryManager->activeTheoryNames();
        }
        caseStats_.enabledStats = {"frontend", "sat", "theory", "search"};

        // Frontend stats
        if (atomizer) {
            const auto& atoms = atomizer->atoms();
            caseStats_.frontend.numAtoms = static_cast<int64_t>(atoms.size());
            int64_t boolAtoms = 0, arithAtoms = 0, eufAtoms = 0;
            for (const auto& a : atoms) {
                if (a.isTheory) {
                    switch (a.theory) {
                        case TheoryId::EUF: ++eufAtoms; break;
                        case TheoryId::LRA:
                        case TheoryId::LIA:
                        case TheoryId::NRA:
                        case TheoryId::NIA:
                        case TheoryId::IDL:
                        case TheoryId::RDL:
                        case TheoryId::LIRA:
                        case TheoryId::NIRA:
                        case TheoryId::Combination:
                            ++arithAtoms; break;
                        default: break;
                    }
                } else {
                    ++boolAtoms;
                }
            }
            caseStats_.frontend.numBoolAtoms = boolAtoms;
            caseStats_.frontend.numArithAtoms = arithAtoms;
            caseStats_.frontend.numEufAtoms = eufAtoms;
        }
        if (registry) {
            caseStats_.frontend.numUnsupported = registry->hasUnsupportedTheoryAtom() ? 1 : 0;
        }
        if (ir) {
            caseStats_.frontend.numExpr = static_cast<int64_t>(ir->assertions().size());
        }

        // SAT stats
        if (cadicalBackend) {
            auto satStats = cadicalBackend->getStats();
            caseStats_.sat.vars = satStats.vars;
            caseStats_.sat.clauses = satStats.clauses;
            caseStats_.sat.conflicts = satStats.conflicts;
            caseStats_.sat.decisions = satStats.decisions;
            caseStats_.sat.propagations = satStats.propagations;
        }

        // Theory stats
        if (theoryManager) {
            const auto& agg = theoryManager->aggregateStats();
            caseStats_.theory.checkCalls = agg.checkCalls;
            caseStats_.theory.conflicts = agg.conflicts;
            caseStats_.theory.lemmas = agg.lemmas;
            caseStats_.theory.propagations = agg.propagations;
            if (agg.conflicts > 0) {
                caseStats_.theory.avgConflictSize = static_cast<double>(agg.totalConflictSize) / agg.conflicts;
            }
            caseStats_.theory.maxConflictSize = agg.maxConflictSize;
        }

        // Search stats (from propagator)
        if (propagator) {
            const auto& ps = propagator->stats();
            caseStats_.search.modelCheckCalls = ps.modelCheckCount;
            caseStats_.search.modelCheckConflicts = ps.modelCheckConflict;
            caseStats_.search.modelCheckLemmas = ps.modelCheckLemma;
            caseStats_.search.modelCheckUnknowns = ps.modelCheckUnknown;

            int totalConflicts = ps.modelCheckConflict + ps.propagateConflictCount;
            long long totalConflictSize = ps.conflictTotalSize + ps.propagateConflictTotalSize;
            caseStats_.search.conflictMinSize = ps.conflictMinSize;
            if (ps.propagateConflictCount > 0) {
                if (caseStats_.search.conflictMinSize < 0 ||
                    ps.propagateConflictMinSize < caseStats_.search.conflictMinSize) {
                    caseStats_.search.conflictMinSize = ps.propagateConflictMinSize;
                }
            }
            caseStats_.search.conflictMaxSize = std::max(ps.conflictMaxSize, ps.propagateConflictMaxSize);
            if (totalConflicts > 0) {
                caseStats_.search.conflictAvgSize = static_cast<double>(totalConflictSize) / totalConflicts;
            }
            caseStats_.search.propagateCalls = ps.propagateCallCount;
            caseStats_.search.propagateTheoryChecks = ps.propagateTheoryCheckCount;
            caseStats_.search.propagateConflicts = ps.propagateConflictCount;
            caseStats_.search.propagateLemmas = ps.propagateLemmaCount;
        }

        if (!dumpStatsPath_.empty()) {
            caseStats_.dumpToFile(dumpStatsPath_);
        }
    }
#endif
#ifdef XOLVER_ENABLE_CASESTATS
    CaseStats caseStats_;
    std::string dumpStatsPath_;
#endif

    Impl() : sat(createSatSolver()) {}

    void reset();

    bool parseFile(std::string_view filename);

    CoreIr& ensureIr();

    SortId getOrCreateBoolSort();

    SortId getOrCreateIntSort();

    SortId getOrCreateRealSort();

    // Portfolio executor (XOLVER_STRAT_PORTFOLIO). Runs the ordered arms from
    // selectPortfolio until one returns a definitive (Sat/Unsat) verdict. Each
    // arm is run from PRISTINE state — the first arm uses the already-parsed
    // problem; subsequent arms reset()+re-parse the source file — so trying
    // several configurations is sound (any arm's Sat/Unsat is already
    // ModelValidator-backed; arms differ only in completeness). Multi-arm needs
    // a re-parseable file source; otherwise (programmatic input) it degrades to
    // a single arm. Phase 1 has one arm == XOLVER_STRAT_PRESETS, so a portfolio
    // run is behavior-neutral until the master populates differentiated arms.
    Result checkSatPortfolio();

    // Run one already-applied arm, optionally under a wall-clock budget. With a
    // positive budget, a watchdog thread async-interrupts the SAT solve once the
    // deadline passes (-> Unknown), so the portfolio falls through to the next
    // arm. budget <= 0 runs the arm to completion thread-free (the default /
    // Phase-1 path, so the common case takes no thread). Interrupting only ever
    // turns a verdict into Unknown, so it can never change a sat/unsat answer.
    Result runArmWithBudget(int budgetMs);

    // Extract an integer value from a ConstInt / int-valued ConstReal node.
    bool extractIntConst(ExprId e, int64_t& out) const;

    // Mark which integer Variables already carry an explicit constant lower /
    // upper bound among the top-level (conjunctive) assertions, and record the
    // largest bound magnitude seen. The escalating bounded SAT fast-path uses
    // these to (a) bound only the *free side* of *free* vars and (b) DERIVE the
    // seed bound from the problem instead of guessing 1,2,4,8.
    void scanIntVarBounds(std::unordered_set<ExprId>& hasLower,
                          std::unordered_set<ExprId>& hasUpper,
                          int64_t& maxBoundMag) const {
        maxBoundMag = 0;
        if (!ir) return;
        SortId intSort = ir->intSortId();
        auto isIntVar = [&](ExprId e) {
            const CoreExpr& n = ir->get(e);
            return n.kind == Kind::Variable && n.sort == intSort;
        };
        auto isConst = [&](ExprId e) {
            const CoreExpr& n = ir->get(e);
            return n.kind == Kind::ConstInt || n.kind == Kind::ConstReal;
        };
        std::vector<ExprId> work = ir->assertions();
        std::unordered_set<ExprId> seen;
        while (!work.empty()) {
            ExprId e = work.back();
            work.pop_back();
            if (!seen.insert(e).second) continue;
            const CoreExpr& n = ir->get(e);
            if (n.kind == Kind::And) {
                for (ExprId c : n.children) work.push_back(c);
                continue;
            }
            if ((n.kind == Kind::Leq || n.kind == Kind::Geq ||
                 n.kind == Kind::Lt  || n.kind == Kind::Gt) &&
                n.children.size() == 2) {
                ExprId a = n.children[0], b = n.children[1];
                ExprId var = NullExpr, cst = NullExpr;
                bool varOnLeft = false;
                if (isIntVar(a) && isConst(b)) { var = a; cst = b; varOnLeft = true; }
                else if (isConst(a) && isIntVar(b)) { var = b; cst = a; varOnLeft = false; }
                if (var != NullExpr) {
                    bool isLe = (n.kind == Kind::Leq || n.kind == Kind::Lt);
                    // var<=c => upper; var>=c => lower; c<=var => lower; c>=var => upper.
                    bool upper = varOnLeft ? isLe : !isLe;
                    if (upper) hasUpper.insert(var); else hasLower.insert(var);
                    int64_t cv;
                    if (extractIntConst(cst, cv)) {
                        int64_t mag = cv < 0 ? -cv : cv;
                        if (mag > maxBoundMag) maxBoundMag = mag;
                    }
                }
            }
        }
    }

    // DERIVE the escalating fast-path's seed bound K0 from the constraints
    // (Cramer / small-model style) instead of guessing. A free integer var
    // coupled linearly to bounded vars satisfies |v| <= M / C, where
    //   M = max magnitude of the bounded vars' explicit bounds, and
    //   C = smallest nonzero coefficient the free vars are multiplied by (the
    //       resolution of the linear coupling, >= 1).
    // Returns K0 >= 1, or 0 if there is no free integer var (fast-path moot).
    long deriveBoundSeed() const;

    // Add  (>= v (- K))  / (<= v K)  for the missing side of every integer
    // Variable that lacks an explicit constant bound there. Returns true iff at
    // least one bound was injected (false => no free integer var => fast-path
    // cannot help). Sound: bounds are only ADDED constraints.
    bool injectFreeIntVarBounds(int K);

    // Sound escalating-bounded SAT fast-path (XOLVER_ESCALATING_BOUNDED_SAT=rounds).
    // The seed bound K0 is DERIVED from the constraints (deriveBoundSeed), not
    // guessed; for `rounds` rounds it solves  original ∪ {free-var bounds in
    // [-K, K]}  with K = K0, 2·K0, 4·K0, ...  A model of the bounded problem
    // satisfies the original (original ⊆ bounded), so a SAT verdict is a sound
    // witness. UNSAT of a box says NOTHING about the original (a witness may lie
    // outside) => escalate, never return UNSAT from the box. Closes formulas
    // whose only obstacle is an unbounded integer var with a bounded-magnitude
    // witness (e.g. GrandProduct β, |β| <= M/C). Needs a re-parseable source.
    Result checkSatEscalatingBoundedSat(int rounds, int perKBudgetMs);

    Result checkSatInternal();


};
} // namespace xolver
