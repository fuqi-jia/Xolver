#include "theory/arith/logics/nra/NraSolver.h"
#include "util/EnvParam.h"
#include "util/SolveClock.h"
#include <chrono>
#include "theory/arith/Reasoner.h"
#include "theory/arith/kernel/linear/LinearExpr.h"
#include "theory/arith/kernel/presolve/Presolve.h"
#include "theory/arith/kernel/poly/RationalPolynomial.h"
#include "util/RealValue.h"                                // XOLVER_NRA_SUBTROPICAL witness model
#include "theory/arith/logics/nra/NraLinearizationAdapter.h"     // XOLVER_NRA_LINEARIZE cut-feeder
#include "theory/arith/logics/nia/preprocess/NiaNormalizer.h"    // XOLVER_NRA_LINEARIZE: normalize nonlinear cstrs
#include "theory/arith/logics/nra/reasoners/SubtropicalSatFinder.h"  // XOLVER_NRA_SUBTROPICAL SAT-fast-path
#include "theory/arith/logics/nra/StructuralIntegerProbe.h"          // XOLVER_NRA_INT_PROBE
#include "theory/arith/logics/nra/NraSquareSolver.h"                   // algebraic square-cascade
#include "theory/arith/logics/nra/reasoners/NraLocalSearch.h"        // XOLVER_NRA_LOCALSEARCH Phase NRA-LS-A
#include "theory/arith/logics/nra/core/HybridPartitionStats.h"     // Task NRA-HYB Step 1 partition stats
#include "theory/arith/logics/nra/simplex/CertifiedSimplexFacts.h"   // OSF-CDCAC P1
#include "theory/arith/logics/nra/simplex/NraLinearExtractor.h"      // §4.2 classifyConstraints
#include "theory/arith/logics/nra/simplex/SimplexTableauFacts.h"     // §4.2 linearSubsetUnsat
#include "theory/arith/logics/nra/simplex/PolynomialIntervalPruner.h" // OSF-CDCAC P7
#include "theory/arith/kernel/icp/IcpEngineQ.h"                       // XOLVER_NRA_ICP rational ICP engine
#include "theory/arith/kernel/icp/ContractorFactoryQ.h"               // XOLVER_NRA_ICP factory
#include "theory/arith/kernel/icp/IcpTypes.h"                         // XOLVER_NRA_ICP IcpConstraint
#include "theory/arith/logics/nra/cac/CacEngine.h"                    // XOLVER_NRA_CAC conflict-driven coverings
#include "theory/arith/logics/nra/core/CdcacCommon.h"                 // #63 relationHolds() for rational-fallback
#include "theory/arith/kernel/refute/SignDefinitenessRefuter.h"       // XOLVER_NRA_SIGN_REFUTE
#include "theory/arith/logics/nra/core/CdcacCore.h"               // XOLVER_NRA_PREELIM reduced CDCAC
#include "theory/arith/logics/nra/core/CdcacConstraint.h"         // XOLVER_NRA_PREELIM
#include "theory/arith/logics/nra/engine/ReasonManager.h"         // XOLVER_NRA_PREELIM conflict reasons
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/logics/nra/backend/LibpolyBackend.h"       // XOLVER_NRA_PREELIM algebra backend
#include "theory/arith/logics/nra/reasoners/NlaCutsRunner.h"             // XOLVER_NRA_NLA_CUTS Phase C-2 hook
#endif
#include <cstdlib>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <fstream>
#include <iostream>

namespace xolver {

NraSolver::NraSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)),
      converter_(std::make_unique<PolynomialConverter>(*kernel_)),
      engine_(kernel_.get()),
      groebner_(*kernel_) {
    enableGroebner_ = xolver::env::flag("XOLVER_NRA_GROBNER");
    cdcacMaxVars_ = xolver::env::paramInt("XOLVER_NRA_CDCAC_MAX_VARS", 0);
    cdcacMaxDeg_  = xolver::env::paramInt("XOLVER_NRA_CDCAC_MAX_DEGREE", 0);
    // Phase 2 reasoner pipeline: presolve fixpoint, then CDCAC.
    // NRA-MGC-PROFILE diagnostic: env-gated per-stage wall-time accounting.
    // Set XOLVER_NRA_STAGE_TIMING=1 for per-stage cumulative on exit.
    // Set XOLVER_NRA_STAGE_TRACE=1 for real-time per-call logging (slower).
    auto stageWrap = [this](const char* name, auto fn) {
        return [this, name, fn](TheoryLemmaStorage& db, TheoryEffort e)
                -> std::optional<TheoryCheckResult> {
            static const bool timing = xolver::env::diag("XOLVER_NRA_STAGE_TIMING");
            static const bool trace = xolver::env::diag("XOLVER_NRA_STAGE_TRACE");
            // File trace (XOLVER_NRA_STAGE_TRACE_FILE=path): the CLI runs the solve
            // on a worker thread whose stderr is suppressed AND the destructor
            // summary never surfaces on a timeout — so neither STAGE_TIMING nor
            // STAGE_TRACE is observable for the slow/TO cases that matter. A
            // per-call file append (flushed) survives both suppression and SIGKILL,
            // making upstream-stage profiling of TO'd QF_NRA cases possible.
            static const char* traceFile = std::getenv("XOLVER_NRA_STAGE_TRACE_FILE");
            if (!timing && !trace && !traceFile) return fn(db, e);
            auto t0 = std::chrono::steady_clock::now();
            auto result = fn(db, e);
            auto t1 = std::chrono::steady_clock::now();
            auto us = std::chrono::duration_cast<std::chrono::microseconds>(t1 - t0).count();
            stageTimingUs_[name] += us;
            stageTimingCalls_[name] += 1;
            if (trace) {
                const char* effortName = (e == TheoryEffort::Full) ? "Full" : "Std";
                std::fprintf(stderr, "[STAGE_TRACE] %s effort=%s %ld us total=%.1f ms\n",
                             name, effortName, (long)us, stageTimingUs_[name] / 1000.0);
                std::fflush(stderr);
            }
            if (traceFile) {
                std::FILE* f = std::fopen(traceFile, "a");
                if (f) {
                    std::fprintf(f, "%-14s %ld us  cumulative=%.1f ms  calls=%llu\n",
                                 name, (long)us, stageTimingUs_[name] / 1000.0,
                                 (unsigned long long)stageTimingCalls_[name]);
                    std::fclose(f);   // close-per-call → survives a later SIGKILL
                }
            }
            return result;
        };
    };

    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.presolve",
        stageWrap("presolve", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stagePresolve(db, e); })));
    // Step 2.1 GLOBAL box-consistency refutation, EARLY (right after presolve, before
    // the covering engines): decides bound-contradiction families (hong) in ~ms,
    // short-circuiting the covering-tree blowup that stageCac would otherwise spend
    // 10s+ on. Sound (interval over-approximation). Default-on, no flag/budget.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.box-refute",
        stageWrap("box-refute", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageBoxRefute(db, e); })));
    // §4.2 linear-subset UNSAT pre-check (XOLVER_NRA_LINEAR_SUBSET_UNSAT,
    // default OFF). If the linear subset of presolveConstraints_ is
    // already simplex-UNSAT, emit a SAT-level conflict over those atoms'
    // SAT lits and short-circuit the CAC/CDCAC engines. Sound: the
    // reasons are original active literals, not NLSAT prefix values
    // (§15.1). nullopt at the gate when OFF.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.linear-subset-unsat",
        stageWrap("linear-subset-unsat",
                  [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageLinearSubsetUnsat(db, e); })));
    // XOLVER_NRA_ICP (default OFF): orthogonal interval-propagation probe,
    // between presolve (linear) and sign-refute (sign). Cheap univariate
    // narrowing; nullopt at the gate when OFF.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.icp",
        stageWrap("icp", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageIcpProbe(db, e); })));
    // XOLVER_NRA_SIGN_REFUTE (default OFF): cheap positive-orthant sign-
    // definiteness UNSAT refuter, right after presolve. nullopt at the gate when OFF.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.sign-refute",
        stageWrap("sign-refute", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageSignRefute(db, e); })));
    // XOLVER_NRA_GROBNER (default OFF): cross-equation ideal-saturation refuter.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.groebner",
        stageWrap("groebner", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageGroebner(db, e); })));
    // XOLVER_NRA_SIGN_SPLIT (default OFF): case-split on sign-blocking variables
    // when sign-refute can't fire. See NDEEP-3/4 / MGC R&D audit.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.sign-split",
        stageWrap("sign-split", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageNraSignSplit(db, e); })));
    // OSF-CDCAC P7: polynomial interval pruning right after sign-split, before
    // linearize. XOLVER_NRA_OSF_PRUNE default-OFF.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.osf-prune",
        stageWrap("osf-prune", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageOsfPrune(db, e); })));
    // XOLVER_NRA_INT_PROBE — moved BEFORE linearize so value-split hints
    // (`(= vv3 2) | (< vv3 2) | (> vv3 2)`) hit SAT BEFORE linearize's
    // LRA sibling resolves its first model. In the SAT branch that picks
    // `= 2`, LRA's model includes vv3=2 from the start → linearize cuts
    // get tangented around an informative base-var point instead of
    // around all-zero, which is what made the loop bail at round=1.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.int-probe-early",
        stageWrap("int-probe-early", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageIntegerProbe(db, e); })));
    // XOLVER_NRA_EQ_CASCADE (default ON; XOLVER_NRA_EQ_CASCADE=0 disables):
    // equality-cascade SAT solver for mgc-class systems — assign the high-degree
    // generator vars, collapse the residual equalities to linear, derive the
    // rest, validate exactly. Sibling of int-probe; runs before linearize so a
    // found model short-circuits CDCAC.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.eq-cascade",
        stageWrap("eq-cascade", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCascade(db, e); })));
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.square-cascade",
        stageWrap("square-cascade", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageSquareCascade(db, e); })));
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.linearize-probe",
        stageWrap("linearize", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageLinearizeProbe(db, e); })));
    // XOLVER_NRA_PREELIM (default OFF): affine pre-elimination then reduced CDCAC.
    // Runs BEFORE the full-variable CDCAC backstop; nullopt at the gate when OFF.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.preelim",
        stageWrap("preelim", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageNraPreElim(db, e); })));
    // XOLVER_NRA_SUBTROPICAL (default OFF): cheap SAT-fast-path before the full
    // CAD. nullopt at the gate when OFF; runs only at Full effort.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.subtropical",
        stageWrap("subtropical", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageSubtropical(db, e); })));
    // (XOLVER_NRA_INT_PROBE now registered EARLY above, before linearize.
    //  Per-var dedup via intProbeValueSplitDone_ makes a second registration
    //  here harmless but redundant; removed.)
    // Sprint 3 (#69): LS pre-pass now runs from NraSolver::check() override
    // ABOVE the Reasoner pipeline so it executes BEFORE CDCAC. The old
    // stageLocalSearch stage was reach-limited (CDCAC hung at Standard before
    // the stage's Full-only LS could fire). Removed from the pipeline.
    // XOLVER_NRA_CAC (A/B for the Collins-vs-CAC differential): conflict-driven
    // single-cell CAC as the primary engine, BEFORE the Collins buildClosure.
    // nullopt at the gate when OFF or on CAC-Unknown ⇒ Collins fallback.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.cac",
        stageWrap("cac", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCac(db, e); })));
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.cdcac",
        stageWrap("cdcac", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCdcac(db, e); })));

    // XOLVER_NRA_PREELIM: read the gate once at construction (mirrors A7's
    // enableCdcac_). OFF ⇒ stageNraPreElim returns nullopt immediately so the
    // default path is byte-identical.
    if (const char* e = std::getenv("XOLVER_NRA_PREELIM"); e && *e && *e != '0')
        enablePreElim_ = true;
    // SUBTROPICAL / CAC / SIGN_REFUTE promoted to default-ON (members default true).
}

// Out-of-line: NraLinearizationAdapter is an incomplete type in the header.
NraSolver::~NraSolver() {
    if (std::getenv("XOLVER_NRA_STAGE_TIMING") && !stageTimingUs_.empty()) {
        // Sort stages by total time descending.
        std::vector<std::pair<std::string, uint64_t>> rows(stageTimingUs_.begin(), stageTimingUs_.end());
        std::sort(rows.begin(), rows.end(),
                  [](const auto& a, const auto& b) { return a.second > b.second; });
        std::fprintf(stderr, "[XOLVER_NRA_STAGE_TIMING] per-stage cumulative:\n");
        for (const auto& [name, us] : rows) {
            auto calls = stageTimingCalls_[name];
            std::fprintf(stderr, "  %-12s  %10.3f ms   %6llu calls   avg %8.1f us\n",
                         name.c_str(),
                         us / 1000.0,
                         (unsigned long long)calls,
                         calls > 0 ? (double)us / calls : 0.0);
        }
    }
}

void NraSolver::setRegistry(TheoryAtomRegistry* reg) {
    registry_ = reg;
    if (reg) {
        linAdapter_ = std::make_unique<NraLinearizationAdapter>(*kernel_, reg);
    }
}

void NraSolver::onPush() {
    scopeStack_.push_back(activeLits_.size());
    engine_.push();
}

void NraSolver::onPop(uint32_t n) {
    for (uint32_t i = 0; i < n && !scopeStack_.empty(); ++i) {
        size_t targetSize = scopeStack_.back();
        scopeStack_.pop_back();
        activeLits_.resize(targetSize);
    }
    trail_.clear();  // V5: rebuild trail from activeLits on next backtrack
    activeSet_.rebuildFromActive(activeLits_, [](const auto& lit) { return lit; });
    presolveConstraints_.resize(activeLits_.size());
    activeRecords_.resize(activeLits_.size());
    satFastModel_.reset();  // XOLVER_NRA_SUBTROPICAL: assignment changed → witness stale
    deducedSharedEqEmitted_.clear();  // #43: dedup window scoped to current SAT
    satCacAlgModel_.reset();  // #55 Phase B: CAC algebraic SAT model stale
    engine_.pop(n);
}

void NraSolver::onReset() {
    engine_.reset();
    activeLits_.clear();
    trail_.clear();
    presolveConstraints_.clear();
    activeRecords_.clear();
    scopeStack_.clear();
    activeSet_.reset();
    interfaceEqualities_.clear();
    interfaceDisequalities_.clear();
    signSplitDone_.clear();   // XOLVER_NRA_SIGN_SPLIT: fresh per solve
    intProbeValueSplitDone_.clear();  // XOLVER_NRA_INT_PROBE: fresh per solve
    satFastModel_.reset();  // XOLVER_NRA_SUBTROPICAL
    deducedSharedEqEmitted_.clear();  // #43: dedup window scoped to current SAT
    satCacAlgModel_.reset();  // #55 Phase B: CAC algebraic SAT model stale
    linRefineRound_ = 0;  // XOLVER_NRA_LINEARIZE: restart refinement budget
    // Phase 4: reset perturbation tracker; new search restart, fresh stuck-state.
    lastLinFp_ = mpq_class(-1);
    linStuckRounds_ = 0;
    linLastNewCuts_ = -1;
    linPerturbSeed_ = 0;
    // Phase NRA-LS-A: per-solve LS state — one-shot gate + statistics.
    lsAttempted_ = false;
    lsTotalMs_ = 0;
    lsCandidatesFound_ = 0;
    lsExactSats_ = 0;
    lsCachedCandidate_.reset();   // Sprint 3: clear persistent LS cache per solve
    // XOLVER_NRA_PREELIM: the reduced core holds no cross-search state (rebuilt
    // per solve), but drop it so a reset releases the libpoly backend too.
    preElimCore_.reset();
    preElimAlgebra_.reset();
    cacBackend_.reset();   // XOLVER_NRA_CAC: release the CAC libpoly backend
}

// Sprint 3: per-solve LS pre-pass via check() override. Runs ONCE per solve
// (on the FIRST entry, any effort) with the current active set, BEFORE the
// Reasoner pipeline / CDCAC. If LS finds a rational candidate that exact-
// validates against every active constraint, the candidate is cached in
// `lsCachedCandidate_` (persistent across cb_propagate — NOT cleared by
// assertLit) and stashed into `satFastModel_` for the verdict path. On every
// subsequent check() the cached candidate is re-validated against the current
// active set; if it still satisfies, we re-stash and return consistent — so
// LS contributes the model only when the SAT search converges on an atom set
// the LS candidate already satisfied. Sound under invariant 1: every emitted
// consistent() is backed by an exact-kernel sign check on every active atom.
TheoryCheckResult NraSolver::check(TheoryLemmaStorage& lemmaDb,
                                   TheoryEffort effort) {
    // Task Q: XOLVER_NRA_LOCALSEARCH promoted source-default-ON; getenv
    // guard removed (no env string in binary). Pre-promotion baseline lived
    // at commit eff76fa; master GREEN-LIT on Task I polypaver +9pp data.

    // Task NRA-HYB Step 1: optional partition-stats dump. Report-only;
    // does not modify solver state. One-shot per solve (first check entry).
    static thread_local int hybStatsLastDumpedSize = -1;
    if (std::getenv("XOLVER_NRA_HYB_PARTITION_STATS") &&
        static_cast<int>(presolveConstraints_.size()) != hybStatsLastDumpedSize) {
        std::vector<PolyId> activePolys;
        activePolys.reserve(presolveConstraints_.size());
        for (const auto& c : presolveConstraints_) activePolys.push_back(c.poly);
        const auto partition = computePartition(activePolys, *kernel_);
        maybeDumpPartitionReport(partition);
        hybStatsLastDumpedSize = static_cast<int>(presolveConstraints_.size());
    }

    // Helper: exact-validate a rational assignment against every active
    // polynomial constraint via the kernel sign.
    auto validateCandidate = [&](const std::unordered_map<VarId, mpq_class>& cand) -> bool {
        std::unordered_map<std::string, mpq_class> evalModel;
        evalModel.reserve(cand.size());
        for (const auto& [v, q] : cand)
            evalModel.emplace(std::string(kernel_->varName(v)), q);
        for (const auto& c : presolveConstraints_) {
            if (c.poly == NullPoly) return false;
            std::unordered_map<std::string, mpq_class> em = evalModel;
            for (const auto& vn : kernel_->variables(c.poly))
                em.emplace(vn, mpq_class(0));   // 0-fill defensively
            const int s = kernel_->sgn(c.poly, em);
            bool ok = false;
            switch (c.rel) {
                case Relation::Eq:  ok = (s == 0); break;
                case Relation::Geq: ok = (s >= 0); break;
                case Relation::Leq: ok = (s <= 0); break;
                case Relation::Gt:  ok = (s > 0);  break;
                case Relation::Lt:  ok = (s < 0);  break;
                case Relation::Neq: ok = (s != 0); break;
            }
            if (!ok) return false;
        }
        return true;
    };

    // 1. If we have a cached candidate from a prior call, re-validate it
    //    against the up-to-date active set first (the cheap path).
    if (lsCachedCandidate_ && validateCandidate(*lsCachedCandidate_)) {
        satFastModel_ = *lsCachedCandidate_;
        return TheoryCheckResult::consistent();
    } else if (lsCachedCandidate_) {
        lsCachedCandidate_.reset();   // re-validation failed — drop stale cache
    }

    // 2. One-shot LS pre-pass. Combination mode (interface (dis)equalities)
    //    routes through the existing N-O pipeline; LS would solve the wrong
    //    problem here. Pure NRA only.
    if (!lsAttempted_ &&
        interfaceEqualities_.empty() && interfaceDisequalities_.empty()) {
        lsAttempted_ = true;
        std::vector<NraLocalSearch::Constraint> lsCons;
        std::set<VarId> varSet;
        bool poly_ok = true;
        for (const auto& c : presolveConstraints_) {
            if (c.poly == NullPoly) { poly_ok = false; break; }
            auto termsOpt = kernel_->terms(c.poly);
            if (!termsOpt) { poly_ok = false; break; }
            lsCons.push_back({c.poly, c.rel, c.reason});
            for (const auto& t : *termsOpt)
                for (const auto& [v, e] : t.powers) varSet.insert(v);
        }
        if (poly_ok && !lsCons.empty() && !varSet.empty()) {
            // One-shot pre-pass budget (#NRA-LS-E). Raised from the 50ms/50-round
            // scaffold to 250ms/3000 rounds: the WalkSAT model search needs the
            // larger round count to reach genuine SAT regions, and this runs
            // BEFORE the (sometimes-spinning, occasionally libpoly-SIGSEGV-ing)
            // CDCAC/Collins pipeline — so for SAT cases it short-circuits the
            // expensive engine entirely (recovers the Economics-Mulligan SAT
            // gaps; one of them, …0061e, otherwise crashes the pipeline). UNSAT
            // cases pay near-zero: WalkSAT converges/plateaus and returns long
            // before the budget (e.g. zankl gen-13 UNSAT: 165ms vs 163ms at the
            // old scaffold). Still one-shot (lsAttempted_), still exact-validated
            // (validateCandidate → invariant 1: SAT only on a kernel-checked
            // model, never UNSAT). Tunable via the env::param registry; raise
            // XOLVER_NRA_LS_BUDGET_MS (e.g. 10000) to also reach the larger
            // zankl-matrix SAT cluster in a wall-clock-anytime profile.
            static const long budgetMs =
                env::paramLong("XOLVER_NRA_LS_BUDGET_MS", 250);
            static const int maxRounds =
                env::paramInt("XOLVER_NRA_LS_MAX_ROUNDS", 3000);
            std::vector<VarId> vars(varSet.begin(), varSet.end());
            static const bool eqRelax = [] {
                return xolver::env::flag("XOLVER_NRA_LS_EQ_RELAX");
            }();
            NraLocalSearch ls(*kernel_);
            // Wall-clock-anytime scaling (#NRA-LS-E iter 3). INERT by default:
            // wall::scaled* return the base unchanged unless XOLVER_WALLCLOCK_SCALE
            // is on AND a deadline (XOLVER_WALLCLOCK_MS) is set — so the default
            // gate is byte-identical. In a competition profile (per-instance
            // ~1200s) the budget grows to ~12s and the round cap to ~60k, which
            // recovers the larger zankl-matrix / Geogebra SAT clusters that need
            // a longer WalkSAT run (matrix-1-all-30 found at ~5s). SAT-only +
            // exact-validated ⇒ growing the search budget never affects a verdict,
            // only how long it looks (mirrors the CAC-deadline scaling at the
            // CacEngine config below).
            //
            // SHARE = 1/10 of the instance wall-clock (was 1/100). The cell-jump
            // escape (LS-NRA critical move) makes WalkSAT the productive engine for the
            // bilinear matrix SAT walls the covering/MCSAT can't touch, but it needs
            // real time: at 1/100 (~12s of a 1200s instance) only the easiest residual
            // cracks; the cell-jump-reachable cases need the larger budget. 1/10 (~120s)
            // is a deliberate front-load for the SAT-finder. SOUND: SAT-only + exact-
            // validated, so a bigger budget never changes a verdict, only how long the
            // search looks; an UNSAT case (WalkSAT has no plateau-exit) pays the slice
            // then falls through to the covering with the remaining 9/10. INERT by
            // default (returns the 250ms base unless XOLVER_WALLCLOCK_SCALE + _MS are
            // set), so the WSL/regression path is byte-identical — this only sizes the
            // competition budget. The round cap is scaled hard (ref 6s, 256x) so the
            // WALL-CLOCK time, not the round count, is the binding limit.
            ls.setBudgetMs(wall::scaledBudgetMs(budgetMs, 1, 10));
            ls.setMaxRounds(static_cast<int>(wall::scaledCount(maxRounds, 6000, 256)));
            ls.setEqRelax(eqRelax);
            const auto t0 = std::chrono::steady_clock::now();
            auto candOpt = ls.tryFindModel(lsCons, vars);
            const auto t1 = std::chrono::steady_clock::now();
            lsTotalMs_ +=
                std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count();
            if (candOpt) {
                ++lsCandidatesFound_;
                if (validateCandidate(*candOpt)) {
                    ++lsExactSats_;
                    lsCachedCandidate_ = *candOpt;
                    satFastModel_ = std::move(*candOpt);
                    return TheoryCheckResult::consistent();
                }
            }
        }
    }

    // 3. Fall through to the normal Reasoner pipeline.
    return ArithSolverBase::check(lemmaDb, effort);
}

void NraSolver::assertLit(const TheoryAtomRecord& atom, bool value,
                          int level, SatLit reason) {
    // Facade-level dedup: same polarity already active → ignore.
    // Opposite polarity is left to the engine's defense-in-depth check.
    if (activeSet_.contains(reason)) {
        return;
    }
    activeSet_.insert(reason);
    satFastModel_.reset();  // XOLVER_NRA_SUBTROPICAL: assignment changed → witness stale
    deducedSharedEqEmitted_.clear();  // #43: dedup window scoped to current SAT
    satCacAlgModel_.reset();  // #55 Phase B: CAC algebraic SAT model stale

    size_t oldSize = activeLits_.size();
    activeLits_.push_back(reason);
    trail_.push_back({level, oldSize});
    // XOLVER_NRA_LINEARIZE: capture full record (one per assertLit, kept aligned
    // with activeLits_/presolveConstraints_ via the same resize() in backtrack/pop).
    activeRecords_.push_back({reason, atom, value});

    const auto* payload = std::get_if<PolynomialAtomPayload>(&atom.payload);
    if (!payload) {
        // Payload mismatch is an internal routing error, NOT a theory conflict.
        // Engine will see this as unsupported and return Unknown.
        presolveConstraints_.push_back({NullPoly, Relation::Eq, reason});  // keep aligned
        engine_.reset();
        return;
    }

    // Algebraic RHS is not representable in the rational polynomial kernel;
    // it never arises from rational inputs. Treat as unsupported → Unknown.
    auto rhsQ = payload->rhs.tryAsRational();
    if (!rhsQ) {
        presolveConstraints_.push_back({NullPoly, Relation::Eq, reason});  // keep aligned
        engine_.reset();
        return;
    }

    Relation rel = value ? payload->rel : negateRelation(payload->rel);
    // Presolve sees the constraint in `p rel 0` form (subtract rhs if present).
    PolyId diff = payload->poly;
    if (*rhsQ != 0) diff = kernel_->sub(payload->poly, kernel_->mkConst(*rhsQ));
    presolveConstraints_.push_back({diff, rel, reason});
    engine_.assertConstraint(payload->poly, rel, reason, level);
}

void NraSolver::onBacktrack(int level) {
    const size_t activeBefore = activeLits_.size();
    while (!trail_.empty() && trail_.back().level > level) {
        activeLits_.resize(trail_.back().activeSizeBefore);
        trail_.pop_back();
    }
    activeSet_.rebuildFromActive(activeLits_, [](const auto& lit) { return lit; });
    presolveConstraints_.resize(activeLits_.size());
    activeRecords_.resize(activeLits_.size());
    // #55 Phase B: only invalidate the SAT stash when backtrack ACTUALLY shrank
    // the trail. CaDiCaL may call notify_backtrack(currentLevel_) at the end of
    // solve() — a no-op for trail/state, but unconditional reset() would destroy
    // the just-stashed CAC/subtropical SAT model right before getModel() runs,
    // turning genuine SAT verdicts into Indeterminate model-validation downgrades
    // (the meti-tarski/sqrt cluster: sqrt-1mcosq-7-chunk-0027/0244/0453 recover).
    const bool shrank = activeLits_.size() < activeBefore;
    if (shrank) {
        satFastModel_.reset();  // XOLVER_NRA_SUBTROPICAL: assignment changed → witness stale
        deducedSharedEqEmitted_.clear();  // #43: dedup window scoped to current SAT
        satCacAlgModel_.reset();  // #55 Phase B: CAC algebraic SAT model stale
    }
    engine_.backtrack(level);
    linRefineRound_ = 0;  // XOLVER_NRA_LINEARIZE: restart refinement budget
    // Phase 4: reset perturbation tracker; new search restart, fresh stuck-state.
    lastLinFp_ = mpq_class(-1);
    linStuckRounds_ = 0;
    linLastNewCuts_ = -1;
    linPerturbSeed_ = 0;
    auto ieIt = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceEqualities_.erase(ieIt, interfaceEqualities_.end());
    auto idIt = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceDisequalities_.erase(idIt, interfaceDisequalities_.end());
}


TheoryCheckResult NraSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {
    if (!sharedTermRegistry_ || !coreIr_ || !converter_)
        return TheoryCheckResult::consistent();
    const auto* stA = sharedTermRegistry_->get(a);
    const auto* stB = sharedTermRegistry_->get(b);
    if (!stA || !stB) return TheoryCheckResult::consistent();

    auto cc = converter_->convertConstraint(stA->coreExpr, stB->coreExpr,
                                            Relation::Eq, *coreIr_);
    if (cc.status == PolyConstraintStatus::Tautology)
        return TheoryCheckResult::consistent();
    if (cc.status == PolyConstraintStatus::Conflict)
        return TheoryCheckResult::mkConflict(TheoryConflict{{reason}});
    if (!cc.isConstraint())
        return TheoryCheckResult::consistent();

    engine_.assertConstraint(cc.diff, Relation::Eq, reason, level);
    interfaceEqualities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

TheoryCheckResult NraSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {
    if (!sharedTermRegistry_ || !coreIr_ || !converter_)
        return TheoryCheckResult::consistent();
    const auto* stA = sharedTermRegistry_->get(a);
    const auto* stB = sharedTermRegistry_->get(b);
    if (!stA || !stB) return TheoryCheckResult::consistent();

    auto cc = converter_->convertConstraint(stA->coreExpr, stB->coreExpr,
                                            Relation::Neq, *coreIr_);
    if (cc.status == PolyConstraintStatus::Tautology)
        return TheoryCheckResult::consistent();
    if (cc.status == PolyConstraintStatus::Conflict)
        return TheoryCheckResult::mkConflict(TheoryConflict{{reason}});
    if (!cc.isConstraint())
        return TheoryCheckResult::consistent();

    engine_.assertConstraint(cc.diff, Relation::Neq, reason, level);
    interfaceDisequalities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

std::vector<TheorySolver::SharedEqualityPropagation>
NraSolver::getDeducedSharedEqualities() {
    // #43: combination-aware CAC SAT — emit pairwise shared-term equalities
    // deduced from the current SAT model. The N-O arrangement-completion seam.
    //
    // Gated XOLVER_NRA_CAC_COMB_SAT, default OFF (master/EQNA opt-in: turn ON
    // alongside XOLVER_NRA_CAC_COMBINATION when the combination loop is
    // configured to consume our deductions). When OFF returns {} — pre-#43
    // behaviour, SAT under combination defers to Collins.
    //
    // Algorithm: for each shared term, convert its CoreIr expression to a
    // polynomial via the same `converter_` path that `assertInterfaceEquality`
    // uses; substitute every variable from `satFastModel_` (the rational SAT
    // sample); the residual must be a constant (else the shared term has
    // unmodelled variables and we skip). Group shared terms by value; within
    // each value-class emit pairwise equalities. SOUND because the SAT model
    // satisfies every asserted lifted constraint, so value(a)==value(b) means
    // (a == b) holds in the model — propagating that as a deduced equality
    // is a tightening of the arrangement, never a contradiction.
    static const bool combSat = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_COMB_SAT");
        return e && *e && *e != '0';
    }();
    std::vector<SharedEqualityPropagation> out;
    if (!combSat) return out;
    if (!sharedTermRegistry_ || !coreIr_ || !converter_) return out;
    if (!satFastModel_ || satFastModel_->empty()) return out;
    // Defensive: when combination-aware CAC is also enabled, emitting deduced
    // equalities can confuse the combination loop (FFT z3.630166 sat→unknown).
    // The COMBINATION + COMB_SAT path keeps the CAC SAT model accessible via
    // satFastModel_ / getModel for model-based arrangement reading, which is the
    // safer route. Skip the explicit propagations in that combination.
    static const bool combination = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_COMBINATION");
        return e && *e && *e != '0';
    }();
    if (combination) return out;

    struct STValue { SharedTermId id; mpq_class value; };
    std::vector<STValue> values;
    auto sharedTermIds = sharedTermRegistry_->allSharedTerms();
    values.reserve(sharedTermIds.size());
    for (SharedTermId id : sharedTermIds) {
        const SharedTerm* st = sharedTermRegistry_->get(id);
        if (!st) continue;
        auto ce = converter_->convert(st->coreExpr, *coreIr_);
        if (!ce.ok()) continue;
        auto rpOpt = RationalPolynomial::fromPolyId(ce.poly, *kernel_);
        if (!rpOpt) continue;
        RationalPolynomial p = std::move(*rpOpt);
        for (const auto& [v, val] : *satFastModel_) {
            p = p.substituteRational(v, val);
        }
        p.normalize();
        if (!p.isConstant()) continue;   // unmodelled variable left; skip
        const mpq_class v0 = p.constantValue() * ce.scale;
        values.push_back({id, v0});
    }

    for (size_t i = 0; i < values.size(); ++i) {
        for (size_t j = i + 1; j < values.size(); ++j) {
            if (values[i].value != values[j].value) continue;
            // Canonical pair (min, max) so the dedup matches regardless of order.
            const SharedTermId a = std::min(values[i].id, values[j].id);
            const SharedTermId b = std::max(values[i].id, values[j].id);
            if (!deducedSharedEqEmitted_.insert({a, b}).second) continue;
            SharedEqualityPropagation prop;
            prop.a = a;
            prop.b = b;
            // Reasons left empty: the deduction holds in the current SAT
            // model, supported by all currently asserted lits. The
            // combination layer scopes the propagation to the current
            // effort context.
            out.push_back(std::move(prop));
        }
    }
    return out;
}

std::optional<TheorySolver::TheoryModel> NraSolver::getModel() const {
    // XOLVER_NRA_SUBTROPICAL: if the SAT-fast-path produced a validated witness
    // for the current assignment, report it (the CDCAC engine was bypassed, so
    // its sample is stale/empty). Exact rational values.
    if (satFastModel_) {
        TheoryModel model;
        for (const auto& [v, val] : *satFastModel_) {
            std::string name(kernel_->varName(v));
            model.numericAssignments.insert({name, RealValue::fromMpq(val)});
            model.assignments[std::move(name)] = val.get_str();
        }
        return model;
    }
    // #55 Phase B: CAC SAT model with algebraic values (XOLVER_NRA_CAC_SAT_ALGEBRAIC).
    if (satCacAlgModel_) {
        TheoryModel model;
        for (const auto& [v, rv] : *satCacAlgModel_) {
            std::string name(kernel_->varName(v));
            model.numericAssignments.insert({name, rv});
            // Legacy string channel: rational => mpq.get_str; algebraic => "alg"
            // marker (Solver.cpp model-validation reads numericAssignments).
            if (rv.isRational()) model.assignments[std::move(name)] = rv.asRational().get_str();
            else model.assignments[std::move(name)] = "alg";
        }
        return model;
    }

    auto sampleOpt = engine_.getModel();
    if (!sampleOpt) return std::nullopt;
    const auto& sample = *sampleOpt;

    TheoryModel model;
    for (size_t i = 0; i < sample.varOrder.size(); ++i) {
        VarId v = sample.varOrder[i];
        const auto& val = sample.values[i];
        std::string name(kernel_->varName(v));
        // Typed channel: exact RealValue (rational or algebraic).
        model.numericAssignments.insert({name, engine_.sampleValueToRealValue(val)});
        // Legacy string channel (retained during the funnel migration).
        std::string valueStr;
        if (val.kind == RealAlg::Kind::Rational) {
            valueStr = val.rational.get_str();
        } else {
            // AlgebraicRoot: strict representation with defining polynomial + isolating interval
            valueStr = engine_.formatAlgebraicRoot(val.root);
        }
        model.assignments[std::move(name)] = std::move(valueStr);
    }
    return model;
}

} // namespace xolver
