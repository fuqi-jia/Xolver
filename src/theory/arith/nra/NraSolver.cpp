#include "theory/arith/nra/NraSolver.h"
#include "util/EnvParam.h"
#include "util/SolveClock.h"
#include <chrono>
#include "theory/arith/Reasoner.h"
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/presolve/Presolve.h"
#include "theory/arith/poly/RationalPolynomial.h"
#include "util/RealValue.h"                                // XOLVER_NRA_SUBTROPICAL witness model
#include "theory/arith/nra/NraLinearizationAdapter.h"     // XOLVER_NRA_LINEARIZE cut-feeder
#include "theory/arith/nia/preprocess/NiaNormalizer.h"    // XOLVER_NRA_LINEARIZE: normalize nonlinear cstrs
#include "theory/arith/nra/reasoners/SubtropicalSatFinder.h"  // XOLVER_NRA_SUBTROPICAL SAT-fast-path
#include "theory/arith/nra/StructuralIntegerProbe.h"          // XOLVER_NRA_INT_PROBE
#include "theory/arith/nra/NraSquareSolver.h"                   // algebraic square-cascade
#include "theory/arith/nra/reasoners/NraLocalSearch.h"        // XOLVER_NRA_LOCALSEARCH Phase NRA-LS-A
#include "theory/arith/nra/search/HybridPartitionStats.h"     // Task NRA-HYB Step 1 partition stats
#include "theory/arith/nra/simplex/CertifiedSimplexFacts.h"   // OSF-CDCAC P1
#include "theory/arith/nra/simplex/NraLinearExtractor.h"      // §4.2 classifyConstraints
#include "theory/arith/nra/simplex/SimplexTableauFacts.h"     // §4.2 linearSubsetUnsat
#include "theory/arith/nra/simplex/PolynomialIntervalPruner.h" // OSF-CDCAC P7
#include "theory/arith/icp/IcpEngineQ.h"                       // XOLVER_NRA_ICP rational ICP engine
#include "theory/arith/icp/ContractorFactoryQ.h"               // XOLVER_NRA_ICP factory
#include "theory/arith/icp/IcpTypes.h"                         // XOLVER_NRA_ICP IcpConstraint
#include "theory/arith/nra/cac/CacEngine.h"                    // XOLVER_NRA_CAC conflict-driven coverings
#include "theory/arith/nra/core/CdcacCommon.h"                 // #63 relationHolds() for rational-fallback
#include "theory/arith/refute/SignDefinitenessRefuter.h"       // XOLVER_NRA_SIGN_REFUTE
#include "theory/arith/nra/core/CdcacCore.h"               // XOLVER_NRA_PREELIM reduced CDCAC
#include "theory/arith/nra/core/CdcacConstraint.h"         // XOLVER_NRA_PREELIM
#include "theory/arith/nra/engine/ReasonManager.h"         // XOLVER_NRA_PREELIM conflict reasons
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/nra/backend/LibpolyBackend.h"       // XOLVER_NRA_PREELIM algebra backend
#include "theory/arith/nra/nla/NlaCutsRunner.h"             // XOLVER_NRA_NLA_CUTS Phase C-2 hook
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
      engine_(kernel_.get()) {
    // Phase 2 reasoner pipeline: presolve fixpoint, then CDCAC.
    // NRA-MGC-PROFILE diagnostic: env-gated per-stage wall-time accounting.
    // Set XOLVER_NRA_STAGE_TIMING=1 for per-stage cumulative on exit.
    // Set XOLVER_NRA_STAGE_TRACE=1 for real-time per-call logging (slower).
    auto stageWrap = [this](const char* name, auto fn) {
        return [this, name, fn](TheoryLemmaStorage& db, TheoryEffort e)
                -> std::optional<TheoryCheckResult> {
            static const bool timing = std::getenv("XOLVER_NRA_STAGE_TIMING") != nullptr;
            static const bool trace = std::getenv("XOLVER_NRA_STAGE_TRACE") != nullptr;
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
                const char* e = std::getenv("XOLVER_NRA_LS_EQ_RELAX");
                return e && *e && *e != '0';
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
            // CacEngine config below; shareDen=100 keeps the up-front slice small
            // so an UNSAT case — WalkSAT has no plateau-exit — front-loads ~12s of
            // a 1200s instance budget, not a 1/4 slice).
            ls.setBudgetMs(wall::scaledBudgetMs(budgetMs, 1, 100));
            ls.setMaxRounds(static_cast<int>(wall::scaledCount(maxRounds)));
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

// Stage 1: theory-check presolve fixpoint (Caps. 1–5, 7, with Real domain).
// May return a Conflict (UNSAT direction) via exact linear/sign reasoning,
// or a Lemma; it never returns SAT directly. nullopt → continue to CDCAC.
//
// Iter#22: per-call wall-clock deadline (parallels NIA's iter#21 deadline
// in stagePresolveFixpoint). Default 50 ms (XOLVER_NRA_PRESOLVE_BUDGET_MS;
// 0 disables). SOUND: the fixpoint's early-exit returns Progress/NoProgress
// based on the partial fact set already in st_.ledger — every recorded
// derivation is still semantically valid; downstream stages (CDCAC, ICP)
// see a SUBSET of what an unbounded run would derive, never an incorrect
// claim. Conflict / Lemma terminations always return immediately.
std::optional<TheoryCheckResult> NraSolver::stagePresolve(TheoryLemmaStorage& /*lemmaDb*/,
                                                          TheoryEffort /*effort*/) {
    static const long presolveBudgetMs =
        env::paramLong("XOLVER_NRA_PRESOLVE_BUDGET_MS", 50);
    PresolveEngine presolve(kernel_.get(), /*integerDomain=*/false);
    bool feasible = true;
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;  // non-polynomial placeholder
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) { feasible = false; break; }
        presolve.addAtom(*rp, c.rel, c.reason);
    }
    if (feasible) {
        auto deadline =
            (presolveBudgetMs > 0)
                ? std::chrono::steady_clock::now() +
                      std::chrono::milliseconds(presolveBudgetMs)
                : std::chrono::steady_clock::time_point::max();
        auto pr = presolve.run(deadline);
        if (pr.kind == PresolveResult::Kind::Conflict)
            return TheoryCheckResult::mkConflict(pr.conflict);
        if (pr.kind == PresolveResult::Kind::Lemma)
            return TheoryCheckResult::mkLemma(pr.lemma);
    }
    return std::nullopt;
}

// §4.2 linear-subset UNSAT pre-check.
//
// Reads presolveConstraints_, classifies them into linear and nonlinear,
// and runs SimplexTableauFacts on the linear subset. If the linear
// subset alone is infeasible, the full NRA query is infeasible — the
// linear contradiction is a sound theory conflict witnessed entirely by
// original active SAT literals.
//
// The conflict clause includes the SAT literals of EVERY linear atom
// (a non-minimal Farkas witness). Sound: the clause `OR ¬lit_i` is
// theory-valid because the conjunction of all linear atoms is UNSAT,
// so at least one lit_i must be false in any model.
//
// Default-OFF — opt-in via XOLVER_NRA_LINEAR_SUBSET_UNSAT=1 until a
// production validation pass measures the perf impact (the simplex runs
// per cb_propagate when enabled).
std::optional<TheoryCheckResult> NraSolver::stageLinearSubsetUnsat(
    TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort /*effort*/) {
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NRA_LINEAR_SUBSET_UNSAT");
        return e && *e && *e != '0';
    }();
    if (!enabled) return std::nullopt;
    if (presolveConstraints_.empty()) return std::nullopt;

    // Build a CdcacConstraint view (skip placeholders). NraSolver's
    // PresolveCstr carries the same {poly, rel, reason} triple — copy
    // the live entries into the shape classifyConstraints wants.
    std::vector<CdcacConstraint> cs;
    cs.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        CdcacConstraint cc;
        cc.poly = c.poly;
        cc.rel = c.rel;
        cc.reason = c.reason;
        cs.push_back(std::move(cc));
    }
    if (cs.empty()) return std::nullopt;

    auto classified = classifyConstraints(*kernel_, cs);
    if (classified.linear.empty()) return std::nullopt;

    auto facts = computeSimplexTableauFacts(*kernel_, classified.linear);
    if (!facts.linearSubsetUnsat()) return std::nullopt;

    // Sound conflict: union all linear-atom SAT lits. At least one must
    // be false in any model since their conjunction is UNSAT.
    TheoryConflict conflict;
    conflict.clause.reserve(classified.linear.size());
    for (const auto& la : classified.linear) {
        conflict.clause.push_back(la.reason);
    }
    if (conflict.clause.empty()) return std::nullopt;
    return TheoryCheckResult::mkConflict(std::move(conflict));
}

// XOLVER_NRA_ICP: rational ICP probe. Sound by construction — emits Conflict
// only when a contractor reports a definitively-violated constraint with
// reasons that union the constraint's reason and the box's bound reasons.
// V1 scope: univariate atoms only. Linear single-var bounds seed the box;
// degree-≥2 single-var polynomials run through RelationContractorQ. Bypassed
// in combination mode (interface (dis)eqs not in presolveConstraints_, matches
// sign-refute's bailout).
std::optional<TheoryCheckResult> NraSolver::stageIcpProbe(TheoryLemmaStorage& /*lemmaDb*/,
                                                          TheoryEffort /*effort*/) {
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NRA_ICP");
        return e && *e && *e != '0';
    }();
    if (!enabled) return std::nullopt;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;

    // Pass 1: seed partial bounds from univariate linear atoms.
    // Closed-interval over-approximation for strict atoms is sound — it only
    // weakens conflict detection, never adds spurious conflicts.
    struct PartialBound {
        bool hasLo = false; mpq_class lo;
        bool hasHi = false; mpq_class hi;
        std::vector<SatLit> reasonsLo;
        std::vector<SatLit> reasonsHi;
    };
    std::unordered_map<std::string, PartialBound> partial;

    auto narrowLo = [&partial](const std::string& v, const mpq_class& val, SatLit r) {
        auto& pb = partial[v];
        if (!pb.hasLo || val > pb.lo) {
            pb.lo = val; pb.reasonsLo.clear();
        }
        if (!pb.hasLo || val >= pb.lo) {
            pb.reasonsLo.push_back(r);
        }
        pb.hasLo = true;
    };
    auto narrowHi = [&partial](const std::string& v, const mpq_class& val, SatLit r) {
        auto& pb = partial[v];
        if (!pb.hasHi || val < pb.hi) {
            pb.hi = val; pb.reasonsHi.clear();
        }
        if (!pb.hasHi || val <= pb.hi) {
            pb.reasonsHi.push_back(r);
        }
        pb.hasHi = true;
    };

    std::vector<IcpConstraint> nonlinearAtoms;
    nonlinearAtoms.reserve(presolveConstraints_.size());

    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        auto vars = kernel_->variables(c.poly);

        if (vars.size() >= 2) {
            // Multivariate: feed to V4 (the factory will discard non-V4
            // shapes). No bound-seeding — V4 reads the rest-vars' boxes
            // populated by the univariate linear pass.
            IcpConstraint ic;
            ic.expr = std::nullopt;
            ic.poly = c.poly;
            ic.rel = c.rel;
            ic.reason = c.reason;
            ic.owner = TheoryId::NRA;
            nonlinearAtoms.push_back(ic);
            continue;
        }
        if (vars.size() != 1) continue;  // 0 vars (constant): handled by presolve

        const std::string& v = vars[0];
        auto degOpt = kernel_->degree(c.poly, v);
        if (!degOpt) continue;

        if (*degOpt == 1) {
            // Linear: c1*x + c0 rel 0  ⇒  bound on x.
            auto coeffsOpt = kernel_->getIntegerCoefficients(c.poly, v);
            if (!coeffsOpt || coeffsOpt->size() != 2) continue;
            const mpz_class& c1 = (*coeffsOpt)[0];
            const mpz_class& c0 = (*coeffsOpt)[1];
            if (c1 == 0) continue;  // shouldn't happen at degree 1, defense-in-depth

            mpq_class bound(-c0, c1);
            bound.canonicalize();
            bool flip = (c1 < 0);

            // After flip, work in the canonical c1>0 frame.
            Relation rel = c.rel;
            switch (rel) {
                case Relation::Eq:
                    narrowLo(v, bound, c.reason);
                    narrowHi(v, bound, c.reason);
                    break;
                case Relation::Leq:
                    if (flip) narrowLo(v, bound, c.reason);
                    else      narrowHi(v, bound, c.reason);
                    break;
                case Relation::Geq:
                    if (flip) narrowHi(v, bound, c.reason);
                    else      narrowLo(v, bound, c.reason);
                    break;
                case Relation::Lt:
                    // Strict over-approximated to non-strict (sound: feasible
                    // set ⊆ closed-interval). No precision loss for sound
                    // conflict detection.
                    if (flip) narrowLo(v, bound, c.reason);
                    else      narrowHi(v, bound, c.reason);
                    break;
                case Relation::Gt:
                    if (flip) narrowHi(v, bound, c.reason);
                    else      narrowLo(v, bound, c.reason);
                    break;
                case Relation::Neq:
                default:
                    break;  // V1: skip (would need disjunctive narrowing)
            }
        } else if (*degOpt >= 2) {
            // Univariate degree ≥ 2 — gather for contractor pass.
            IcpConstraint ic;
            ic.expr = std::nullopt;
            ic.poly = c.poly;
            ic.rel = c.rel;
            ic.reason = c.reason;
            ic.owner = TheoryId::NRA;
            nonlinearAtoms.push_back(ic);
        }
    }

    // Pass 2: build the box only from variables with BOTH endpoints — no
    // infinity sentinel exists in IntervalQ, so a half-bounded var is unsafe
    // for interval polynomial evaluation (would need ±∞ propagation rules).
    ReasonedBoxQ box;
    for (auto& [v, pb] : partial) {
        if (!pb.hasLo || !pb.hasHi) continue;
        if (pb.lo > pb.hi) {
            // Linear seeds alone already proved infeasibility on x — emit the
            // direct conflict; presolve normally catches this too, this is
            // defense-in-depth so ICP never runs over an empty box.
            std::vector<SatLit> reasons = pb.reasonsLo;
            reasons.insert(reasons.end(), pb.reasonsHi.begin(), pb.reasonsHi.end());
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
        }
        std::vector<SatLit> reasons = pb.reasonsLo;
        reasons.insert(reasons.end(), pb.reasonsHi.begin(), pb.reasonsHi.end());
        box.set(v, ReasonedIntervalQ{IntervalQ{pb.lo, pb.hi}, std::move(reasons)});
    }

    // Without any seeded variable, no contractor can fire. Skip the engine.
    if (box.entries().empty()) return std::nullopt;
    if (nonlinearAtoms.empty()) return std::nullopt;

    auto built = ContractorFactoryQ::build(nonlinearAtoms, *kernel_);
    if (built.contractors.empty()) return std::nullopt;

    IcpConfig cfg;  // defaults are fine; budget keeps the worklist bounded
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);
    if (r.status == IcpStatus::Conflict && r.conflict) {
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    return std::nullopt;
}

// XOLVER_NRA_SIGN_REFUTE: positive-orthant sign-definiteness refuter. Cheap,
// unconditionally sound UNSAT for sign-definite constraints (e.g. a sum of
// strictly-positive monomials = 0 with all variables positive — the Sturm-MBO
// family that CAD/CAC time out on).
std::optional<TheoryCheckResult> NraSolver::stageSignRefute(TheoryLemmaStorage& /*lemmaDb*/,
                                                            TheoryEffort /*effort*/) {
    if (!enableSignRefute_) return std::nullopt;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;   // combination: interface (dis)eqs not in presolveConstraints_

    std::vector<SignRefuteConstraint> cs;
    cs.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) continue;     // skip unrepresentable; a missing constraint only loses completeness
        cs.push_back({std::move(*rp), c.rel, c.reason});
    }
    auto conflict = refuteBySignDefiniteness(cs);
    if (!conflict) return std::nullopt;

    TheoryConflict tc;
    tc.clause = std::move(*conflict);
    if (std::getenv("XOLVER_NRA_SIGN_REFUTE_DIAG")) {
        std::ofstream st("/tmp/sign_refute.txt", std::ios::app);
        st << "[SIGN-REFUTE] UNSAT cons=" << cs.size() << " clause=" << tc.clause.size() << "\n";
        st.flush();
    }
    return TheoryCheckResult::mkConflict(std::move(tc));
}

// XOLVER_NRA_SIGN_SPLIT (default OFF). MGC-RD closing lever.
//
// When sign-refute fails because exactly ONE variable's sign is unknown in
// an otherwise-refutable equation/inequality, emit a 3-way case-split
// theory lemma  (or (> v 0) (= v 0) (< v 0))  on that variable. The
// disjunction is a tautology over R (covers every real number), so adding
// it never alters the feasible region — soundness is structural. In each
// branch the variable's sign becomes definite, sign-refute fires.
//
// Per-solve dedup via signSplitDone_; cleared in onReset to enable a fresh
// split set per solve.
std::optional<TheoryCheckResult> NraSolver::stageNraSignSplit(
        TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort /*effort*/) {
    static const bool enabled = []() {
        const char* e = std::getenv("XOLVER_NRA_SIGN_SPLIT");
        return e && *e && *e != '0';
    }();
    if (!enabled) return std::nullopt;
    // Run at every effort: the lemma is a tautology so emitting early
    // (Standard effort) lets SAT branch before propagation digs deep.
    if (!registry_) return std::nullopt;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;
    if (presolveConstraints_.empty()) return std::nullopt;

    // Pass 1: derive known signs from single-var linear bounds (mirrors
    // SignDefinitenessRefuter so we agree on which vars are unknown).
    enum class Sign : uint8_t { Unknown, PosStrict, NegStrict, NonNeg, NonPos };
    std::unordered_map<VarId, Sign> known;
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        auto rpOpt = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rpOpt) continue;
        const auto& rp = *rpOpt;
        const auto vars = rp.variables();
        if (vars.size() != 1) continue;
        const VarId v = *vars.begin();
        if (rp.degree(v) != 1) continue;
        mpq_class coeff = 0, constTerm = 0;
        for (const auto& [mon, k] : rp.terms()) {
            if (mon.empty()) constTerm = k;
            else if (mon.size() == 1 && mon[0].first == v && mon[0].second == 1) coeff = k;
            else { coeff = 0; break; }
        }
        if (coeff == 0) continue;
        mpq_class boundary = -constTerm / coeff;
        Relation rel = c.rel;
        if (coeff < 0) {
            switch (rel) {
                case Relation::Lt:  rel = Relation::Gt; break;
                case Relation::Leq: rel = Relation::Geq; break;
                case Relation::Gt:  rel = Relation::Lt;  break;
                case Relation::Geq: rel = Relation::Leq; break;
                default: break;
            }
        }
        Sign s = Sign::Unknown;
        if (rel == Relation::Gt && boundary >= 0) s = Sign::PosStrict;
        else if (rel == Relation::Geq && boundary > 0) s = Sign::PosStrict;
        else if (rel == Relation::Geq && boundary == 0) s = Sign::NonNeg;
        else if (rel == Relation::Lt && boundary <= 0) s = Sign::NegStrict;
        else if (rel == Relation::Leq && boundary < 0) s = Sign::NegStrict;
        else if (rel == Relation::Leq && boundary == 0) s = Sign::NonPos;
        if (s == Sign::Unknown) continue;
        auto& slot = known[v];
        // Strict wins over non-strict.
        if (slot == Sign::Unknown ||
            ((s == Sign::PosStrict || s == Sign::NegStrict) &&
             !(slot == Sign::PosStrict || slot == Sign::NegStrict))) {
            slot = s;
        }
    }

    // Pass 2: find a sign-blocking variable. Heuristic: pick the unknown-sign
    // variable that appears in the most constraints. Only consider vars that
    // haven't been split before this solve.
    std::unordered_map<VarId, int> unknownVarUseCount;
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        for (const auto& vn : kernel_->variables(c.poly)) {
            auto vid = kernel_->findVar(vn);
            if (!vid) continue;
            if (known.find(*vid) != known.end()) continue;
            if (signSplitDone_.count(*vid)) continue;
            unknownVarUseCount[*vid]++;
        }
    }
    if (unknownVarUseCount.empty()) return std::nullopt;
    VarId pick = NullVar;
    int bestCount = 0;
    for (const auto& [v, n] : unknownVarUseCount) {
        if (n > bestCount) { pick = v; bestCount = n; }
    }
    if (pick == NullVar) return std::nullopt;

    // Emit the 3-way disjunction lemma: (or (> v 0) (= v 0) (< v 0)).
    // Each atom is on (v - 0), i.e. just the poly v.
    PolyId vPoly = kernel_->mkVar(pick);
    SatLit gt = registry_->getOrCreatePolynomialAtom(vPoly, Relation::Gt, mpq_class(0), TheoryId::LRA);
    SatLit eq = registry_->getOrCreatePolynomialAtom(vPoly, Relation::Eq, mpq_class(0), TheoryId::LRA);
    SatLit lt = registry_->getOrCreatePolynomialAtom(vPoly, Relation::Lt, mpq_class(0), TheoryId::LRA);
    if (gt.var == 0 || eq.var == 0 || lt.var == 0) return std::nullopt;

    TheoryLemma lemma{{gt, eq, lt}};
    signSplitDone_.insert(pick);

    if (std::getenv("XOLVER_NRA_SIGN_SPLIT_DIAG")) {
        std::fprintf(stderr,
            "[XOLVER_NRA_SIGN_SPLIT] split on var=%u uses=%d  lemma=(>0 | =0 | <0)\n",
            (unsigned)pick, bestCount);
    }
    return TheoryCheckResult::mkLemma(std::move(lemma));
}

// OSF-CDCAC P7: stageOsfPrune.
//
// Build a CertifiedSimplexFacts from the active single-variable linear
// bounds in presolveConstraints_. Then run polynomial interval pruning:
// for each constraint p rel 0, compute [L, U] via monomial arithmetic.
// If the interval contradicts rel, emit a sound theory conflict.
//
// Distinct from SignDefinitenessRefuter: that one only tracks SIGN
// (Pos/Neg/NonNeg/NonPos), this tracks NUMERIC bounds so constraints
// like x in [2,5] and y in [3,4] propagate through x*y to [6, 20].
//
// Default OFF until paired-validated on broader corpus.
std::optional<TheoryCheckResult> NraSolver::stageOsfPrune(
        TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort /*effort*/) {
    static const bool enabled = []() {
        const char* e = std::getenv("XOLVER_NRA_OSF_PRUNE");
        return e && *e && *e != '0';
    }();
    if (!enabled) return std::nullopt;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;
    if (presolveConstraints_.empty()) return std::nullopt;

    // Build CertifiedSimplexFacts from single-variable linear constraints.
    CertifiedSimplexFacts facts;
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        auto rpOpt = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rpOpt) continue;
        const auto& rp = *rpOpt;
        const auto vars = rp.variables();
        if (vars.size() != 1) continue;
        const VarId v = *vars.begin();
        if (rp.degree(v) != 1) continue;
        mpq_class coeff = 0, constTerm = 0;
        for (const auto& [mon, k] : rp.terms()) {
            if (mon.empty()) constTerm = k;
            else if (mon.size() == 1 && mon[0].first == v && mon[0].second == 1) coeff = k;
            else { coeff = 0; break; }
        }
        if (coeff == 0) continue;
        mpq_class boundary = -constTerm / coeff;
        Relation rel = c.rel;
        if (coeff < 0) {
            switch (rel) {
                case Relation::Lt:  rel = Relation::Gt;  break;
                case Relation::Leq: rel = Relation::Geq; break;
                case Relation::Gt:  rel = Relation::Lt;  break;
                case Relation::Geq: rel = Relation::Leq; break;
                default: break;
            }
        }
        std::vector<SatLit> reasons{c.reason};
        switch (rel) {
            case Relation::Gt:  facts.tightenLower(v, boundary, /*strict=*/true,  reasons); break;
            case Relation::Geq: facts.tightenLower(v, boundary, /*strict=*/false, reasons); break;
            case Relation::Lt:  facts.tightenUpper(v, boundary, /*strict=*/true,  reasons); break;
            case Relation::Leq: facts.tightenUpper(v, boundary, /*strict=*/false, reasons); break;
            case Relation::Eq:
                facts.tightenLower(v, boundary, /*strict=*/false, reasons);
                facts.tightenUpper(v, boundary, /*strict=*/false, reasons);
                break;
            default: break;
        }
    }

    // Build IntervalConstraint list for the multi-var (potentially nonlinear)
    // constraints. Skip the single-var linear ones we already used as bounds
    // (they would trivially refute themselves if inconsistent).
    std::vector<IntervalConstraint> intervalCs;
    intervalCs.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        intervalCs.push_back({c.poly, c.rel, c.reason});
    }
    // First try plain interval refutation (cheap, every call).
    auto conflictOpt = tryRefuteByPolynomialInterval(intervalCs, facts, *kernel_);
    // If no plain conflict, try iterative factoring + back-prop (closes MGC-class).
    // This is the EXPENSIVE part (maxIter back-prop passes over ALL constraints) and
    // re-running it on every Standard cb_propagate during a SAT search is the overhead
    // that times out SAT cases (mgc_09/10: sat→TO; iter 24/25). THROTTLE its cadence:
    // run on the first call (catch quick UNSAT) then only every K-th call. SOUND — a
    // conflict is still found, at most K-1 checks later; SAT cases pay K× less factoring.
    // Tunable XOLVER_NRA_OSF_FACTOR_CADENCE (default 1 = unchanged behaviour).
    static const long factorCadence = []() {
        long v = env::paramInt("XOLVER_NRA_OSF_FACTOR_CADENCE", 1);
        return v > 0 ? v : 1;
    }();
    static thread_local long osfCalls = 0;
    long n = ++osfCalls;
    if (!conflictOpt && (n == 1 || (n % factorCadence) == 0)) {
        conflictOpt = tryRefuteByIterativeFactoring(intervalCs, facts, *kernel_, /*maxIter=*/6);
    }
    if (!conflictOpt) return std::nullopt;

    TheoryConflict tc;
    tc.clause = std::move(conflictOpt->reasons);
    if (std::getenv("XOLVER_NRA_OSF_DIAG")) {
        std::fprintf(stderr, "[XOLVER_NRA_OSF_PRUNE] UNSAT: %s reasons=%zu\n",
                     conflictOpt->explanation.c_str(), tc.clause.size());
    }
    return TheoryCheckResult::mkConflict(std::move(tc));
}

// XOLVER_NRA_PREELIM (default OFF): affine-equality pre-elimination + reduced CDCAC.
//
// CAD (and CDCAC) is doubly-exponential in #variables. The hycomp BMC SAT cases
// couple ~20+ vars, many of which are `_def_*` intermediates defined by LINEAR
// equalities. Eliminating those before CDCAC shrinks the variable count CDCAC
// faces — the lever this stage provides.
//
//   1. Run the presolve fixpoint (integerDomain=false). It records every affine
//      substitution `v = (linear expr over remaining vars)` in substMap, already
//      transitively composed (registerSubstitution reduces values by existing
//      substs and back-substitutes), each tagged with a ledger fact index whose
//      flattenReasons gives the defining-equality SAT literals.
//   2. Substitute every eliminated var out of each ORIGINAL constraint poly.
//   3. Build a reduced CdcacInput (varOrder = remaining vars, lexicographic) and
//      solve with a lazily-built CdcacCore + libpoly backend.
//   4. UNSAT: union EVERY eliminated var's defining-equality reason into the
//      conflict (a superset is sound; omitting one would be a too-strong /
//      false-UNSAT clause — detection-sound ≠ explanation-sound).
//   5. SAT: reconstruct each eliminated var by evaluating its (composed, over
//      remaining vars) defining expr on the solved model, assemble the full real
//      model, and validate over the ORIGINAL presolveConstraints_ via the exact
//      kernel sign (invariant 1 — never return consistent() on the reduced set).
//   6. Unknown / anything unsound to reconstruct ⇒ nullopt (fall to stageCdcac).
//
// Flag OFF ⇒ returns nullopt at the gate (default path byte-identical). No-op
// without XOLVER_HAS_LIBPOLY (CDCAC needs the libpoly algebra backend).
std::optional<TheoryCheckResult> NraSolver::stageNraPreElim(TheoryLemmaStorage& /*lemmaDb*/,
                                                            TheoryEffort /*effort*/) {
    if (!enablePreElim_) return std::nullopt;
#ifndef XOLVER_HAS_LIBPOLY
    return std::nullopt;
#else
    // Collect the live polynomial constraints (skip non-polynomial placeholders).
    std::vector<PresolveCstr> liveCstrs;
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        liveCstrs.push_back(c);
    }
    if (liveCstrs.empty()) return std::nullopt;

    // --- Step 1: presolve fixpoint → affine substitutions. -------------------
    // Same iter#22 deadline as stagePresolve above (this is the preelim path
    // that also calls presolve as Step 1 before CDCAC; identical cost profile,
    // identical 50 ms default cap, identical soundness story).
    static const long preelimPresolveBudgetMs =
        env::paramLong("XOLVER_NRA_PRESOLVE_BUDGET_MS", 50);
    PresolveEngine presolve(kernel_.get(), /*integerDomain=*/false);
    std::vector<std::optional<RationalPolynomial>> rps;  // cached RationalPolynomial per cstr
    rps.reserve(liveCstrs.size());
    for (const auto& c : liveCstrs) {
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) return std::nullopt;  // cannot reason; defer to plain CDCAC
        presolve.addAtom(*rp, c.rel, c.reason);
        rps.push_back(rp);
    }
    auto preelimDeadline =
        (preelimPresolveBudgetMs > 0)
            ? std::chrono::steady_clock::now() +
                  std::chrono::milliseconds(preelimPresolveBudgetMs)
            : std::chrono::steady_clock::time_point::max();
    auto pr = presolve.run(preelimDeadline);
    // A presolve Conflict here is handled by stagePresolve already; if it fires
    // we still emit it (sound). A Lemma is a SAT-core split — defer to the normal
    // pipeline by NOT consuming it here (stagePresolve ran first anyway).
    if (pr.kind == PresolveResult::Kind::Conflict)
        return TheoryCheckResult::mkConflict(pr.conflict);

    const PresolveState& ps = presolve.state();
    // Each entry: eliminated var → (defining expr over remaining vars, reason lits).
    struct Elim { VarId var; RationalPolynomial expr; std::vector<SatLit> reasons; };
    std::vector<Elim> elims;
    for (const auto& [v, entry] : ps.substMap) {
        std::vector<SatLit> reasons = ps.ledger.flattenReasons(entry.factIndex);
        elims.push_back({v, entry.value, std::move(reasons)});
    }
    if (elims.empty()) return std::nullopt;  // nothing to eliminate → plain CDCAC wins

    // --- Step 2: substitute eliminated vars out of each ORIGINAL constraint. --
    // substMap values are already transitively composed over the non-eliminated
    // variables, so a single pass of substitute() per eliminated var suffices.
    CdcacInput input;
    std::unordered_set<std::string> seen;
    std::vector<std::string> varNames;
    for (size_t i = 0; i < liveCstrs.size(); ++i) {
        RationalPolynomial p = *rps[i];
        for (const auto& e : elims) {
            if (p.contains(e.var)) p = p.substitute(e.var, e.expr);
        }
        p.normalize();
        PolyId pid = p.toPolyId(*kernel_);
        if (pid == NullPoly) return std::nullopt;  // conversion failed → defer
        CdcacConstraint cc;
        cc.poly = pid;
        cc.rel = liveCstrs[i].rel;
        cc.reason = liveCstrs[i].reason;
        input.constraints.push_back(std::move(cc));
        for (const auto& vn : kernel_->variables(pid)) {
            if (seen.insert(vn).second) varNames.push_back(vn);
        }
    }
    std::sort(varNames.begin(), varNames.end());
    for (const auto& vn : varNames) input.varOrder.push_back(kernel_->getOrCreateVar(vn));

    {
        std::ofstream pe("/tmp/nrapreelim.txt", std::ios::app);
        pe << "[NRAPREELIM] constraints=" << liveCstrs.size()
           << " eliminated=" << elims.size()
           << " remainingVars=" << input.varOrder.size() << "\n";
        pe.flush();
    }

    // --- Step 3: solve a reduced CDCAC over the remaining variables. ---------
    if (!preElimCore_) {
        preElimAlgebra_ = std::make_unique<LibpolyBackend>(kernel_.get());
        preElimCore_ = std::make_unique<CdcacCore>(kernel_.get(), preElimAlgebra_.get());
    }
    CdcacResult result = preElimCore_->solve(input);

    switch (result.status) {
        case CdcacStatus::Unsat: {
            // Real-relaxation covering-UNSAT over the reduced (substituted) system
            // ⇒ UNSAT of the original (the eliminated vars are functionally pinned
            // by their defining equalities). CdcacCore already downgrades an
            // uncertified covering to Unknown, so a Unsat reaching here is a
            // trustworthy empty-covering proof. Thread in EVERY eliminated var's
            // defining-equality reason (a superset is sound; OMITTING one would be
            // a too-strong / false-UNSAT clause).
            std::vector<SatLit> reasons;
            if (result.unsat) reasons = ReasonManager::minimize(result.unsat->covering);
            for (const auto& e : elims)
                reasons.insert(reasons.end(), e.reasons.begin(), e.reasons.end());
            std::ofstream pe("/tmp/nrapreelim.txt", std::ios::app);
            pe << "[NRAPREELIM] verdict=UNSAT reasons=" << reasons.size() << "\n";
            pe.flush();
            return TheoryCheckResult::mkConflict(ReasonManager::toConflict(reasons));
        }
        case CdcacStatus::Sat: {
            if (!result.model) return std::nullopt;
            const SamplePoint& s = *result.model;
            // Solved model over the remaining vars. Reconstruct eliminated vars by
            // evaluating their (composed, over-remaining-vars) defining expr.
            // Accept ONLY a fully-rational sample (algebraic coordinates can't be
            // reconstructed exactly through substitute/sgn here → defer to CDCAC).
            std::unordered_map<std::string, mpq_class> model;
            for (size_t i = 0; i < s.varOrder.size() && i < s.values.size(); ++i) {
                const RealAlg& v = s.values[i];
                if (!v.isRational()) return std::nullopt;
                model[std::string(kernel_->varName(s.varOrder[i]))] = v.rational;
            }
            // Reconstruct eliminated vars. Their defining exprs are over the
            // remaining (solved) vars only, so a single eval per var is exact.
            for (const auto& e : elims) {
                RationalPolynomial expr = e.expr;
                // Substitute each solved value into expr; result must be constant.
                for (const auto& [name, val] : model) {
                    auto vid = kernel_->findVar(name);
                    if (vid && expr.contains(*vid))
                        expr = expr.substituteRational(*vid, val);
                }
                // Any eliminated var the expr still references (chained def) — fold
                // those too, in case substMap composition left a residual.
                for (const auto& e2 : elims) {
                    if (e2.var == e.var) continue;
                    // Not expected (composed away), but guard: cannot resolve → defer.
                    if (expr.contains(e2.var)) return std::nullopt;
                }
                if (!expr.isConstant()) return std::nullopt;  // can't pin → defer
                model[std::string(kernel_->varName(e.var))] = expr.constantValue();
            }
            // --- Step 5: validate over the ORIGINAL constraints (invariant 1). --
            bool allHold = true;
            for (const auto& c : liveCstrs) {
                std::unordered_map<std::string, mpq_class> evalModel = model;
                for (const auto& vn : kernel_->variables(c.poly))
                    evalModel.emplace(vn, mpq_class(0));  // 0-fill any absent (none expected)
                int sg = kernel_->sgn(c.poly, evalModel);
                bool ok = false;
                switch (c.rel) {
                    case Relation::Eq:  ok = (sg == 0); break;
                    case Relation::Geq: ok = (sg >= 0); break;
                    case Relation::Leq: ok = (sg <= 0); break;
                    case Relation::Gt:  ok = (sg > 0);  break;
                    case Relation::Lt:  ok = (sg < 0);  break;
                    case Relation::Neq: ok = (sg != 0); break;
                }
                if (!ok) { allHold = false; break; }
            }
            std::ofstream pe("/tmp/nrapreelim.txt", std::ios::app);
            pe << "[NRAPREELIM] verdict=SAT validated=" << (allHold ? "yes" : "no") << "\n";
            pe.flush();
            if (allHold) return TheoryCheckResult::consistent();
            return std::nullopt;  // validation failed → fall to plain CDCAC
        }
        case CdcacStatus::Unknown: {
            std::ofstream pe("/tmp/nrapreelim.txt", std::ios::app);
            pe << "[NRAPREELIM] verdict=UNKNOWN reason="
               << static_cast<int>(result.unknownReason) << "\n";
            pe.flush();
            return std::nullopt;
        }
    }
    return std::nullopt;
#endif
}

// XOLVER_NRA_SUBTROPICAL SAT-fast-path (default OFF). A cheap, incomplete
// witness search "at infinity" run before the full CAD. It produces a CANDIDATE
// assignment; every active original constraint is then exact-validated via the
// kernel sign (invariant 1). SAT only on a validated model (stored in
// satFastModel_ so getModel() reports it); otherwise nullopt → fall to CDCAC.
std::optional<TheoryCheckResult> NraSolver::stageSubtropical(TheoryLemmaStorage& /*lemmaDb*/,
                                                             TheoryEffort effort) {
    if (!enableSubtropical_) return std::nullopt;
    if (effort != TheoryEffort::Full) return std::nullopt;  // fast path at full effort only
    // Combination (Nelson-Oppen) mode: interface (dis)equalities live in the
    // engine, not presolveConstraints_, so a witness validated only against the
    // local atoms could violate them. Restrict the fast path to pure NRA.
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;

    // --- Build the subtropical constraint set from the active polynomials. ---
    // Bail (fall through) if ANY active constraint is non-polynomial or cannot be
    // decomposed into integer-coefficient terms: a witness validated only against
    // a SUBSET would be unsound to report as SAT.
    std::vector<SubtropicalConstraint> subCons;
    std::unordered_set<VarId> varSet;
    subCons.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) return std::nullopt;
        auto termsOpt = kernel_->terms(c.poly);
        if (!termsOpt) return std::nullopt;
        SubtropicalConstraint sc;
        sc.rel = c.rel;
        sc.monomials.reserve(termsOpt->size());
        for (const auto& t : *termsOpt) {
            if (t.coefficient == 0) continue;
            SubtropicalMonomial m;
            m.coeff = t.coefficient;
            m.powers = t.powers;
            for (const auto& pr : t.powers) varSet.insert(pr.first);
            sc.monomials.push_back(std::move(m));
        }
        subCons.push_back(std::move(sc));
    }
    if (subCons.empty() || varSet.empty()) return std::nullopt;  // ground / nothing to do

    std::vector<VarId> vars(varSet.begin(), varSet.end());

    SubtropicalSatFinder finder;
    SubtropicalResult r = finder.find(subCons, vars);
    if (!r.found) return std::nullopt;

    // Guard against pathological magnitudes (base^exp blow-up). Sound to skip.
    for (const auto& [v, e] : r.dir.exponents) {
        if (abs(e) > 64) return std::nullopt;
    }

    // --- Materialize over increasing bases and exact-validate (invariant 1). -
    static const long kBases[] = {2, 4, 16, 256, 4096, 65536};
    for (long b : kBases) {
        auto vidModel = SubtropicalSatFinder::materialize(r.dir, vars, mpq_class(b));
        std::unordered_map<std::string, mpq_class> model;
        model.reserve(vidModel.size());
        for (const auto& [v, val] : vidModel) model.emplace(std::string(kernel_->varName(v)), val);

        bool allHold = true;
        for (const auto& c : presolveConstraints_) {
            std::unordered_map<std::string, mpq_class> evalModel = model;
            for (const auto& vn : kernel_->variables(c.poly))
                evalModel.emplace(vn, mpq_class(0));  // 0-fill (defensive)
            const int s = kernel_->sgn(c.poly, evalModel);
            bool ok = false;
            switch (c.rel) {
                case Relation::Eq:  ok = (s == 0); break;
                case Relation::Geq: ok = (s >= 0); break;
                case Relation::Leq: ok = (s <= 0); break;
                case Relation::Gt:  ok = (s > 0);  break;
                case Relation::Lt:  ok = (s < 0);  break;
                case Relation::Neq: ok = (s != 0); break;
            }
            if (!ok) { allHold = false; break; }
        }
        if (allHold) {
            // Sound: a concrete rational point validates ALL active constraints
            // under the exact kernel sign. Stash it so getModel() reports it.
            satFastModel_ = std::move(vidModel);
            if (std::getenv("XOLVER_NRA_SUBTROP_DIAG")) {
                std::ofstream st("/tmp/subtropical.txt", std::ios::app);
                st << "[SUBTROP] SAT vars=" << vars.size()
                   << " cons=" << subCons.size() << " base=" << b << "\n";
                st.flush();
            }
            return TheoryCheckResult::consistent();
        }
    }
    return std::nullopt;  // no base validated: fall through to CDCAC
}

// XOLVER_NRA_INT_PROBE — structural-integer probe (mgc-class SAT-fast-path).
// Sibling of stageSubtropical. Enumerates small integer + dyadic candidates
// for the highest-exponent variables (which z3-nlsat's decision heuristic
// gravitates toward on mgc-style problems), validates each candidate via
// the kernel sign (invariant 1). Pure NRA only; combination/N-O mode falls
// through because interface (dis)equalities live outside presolveConstraints_.
std::optional<TheoryCheckResult> NraSolver::stageIntegerProbe(
        TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort effort) {
    if (std::getenv("XOLVER_NRA_INT_PROBE_DIAG")) {
        std::ofstream dst("/tmp/int_probe.txt", std::ios::app);
        dst << "[INT-PROBE] called effort=" << (int)effort
            << " presolve=" << presolveConstraints_.size() << "\n";
        dst.flush();
    }
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NRA_INT_PROBE");
        return e && *e && *e != '0';
    }();
    if (!enabled) return std::nullopt;
    // Run at FIRST effort entry (typically Standard) — CDCAC may not survive
    // to Full effort on mgc-class. Sound: a kernel-validated rational point
    // is SAT at any effort (invariant 1). One-shot per solve.
    (void)effort;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;
    if (presolveConstraints_.empty()) return std::nullopt;

    // No one-shot lock: each round the probe re-attempts; the value-split
    // hint dedup is per-var in intProbeValueSplitDone_ (cleared on reset).

    bool diagOn = (std::getenv("XOLVER_NRA_INT_PROBE_DIAG") != nullptr);
    std::ofstream st;
    if (diagOn) {
        st.open("/tmp/int_probe.txt", std::ios::app);
        st << "[INT-PROBE] enter; constraints=" << presolveConstraints_.size() << "\n";
        st.flush();
    }

    std::vector<StructuralIntegerProbe::Constraint> cons;
    cons.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) {
            if (diagOn) { st << "[INT-PROBE] NullPoly bail\n"; st.flush(); }
            return std::nullopt;
        }
        cons.push_back({c.poly, c.rel});
    }

    auto modelOpt = StructuralIntegerProbe::tryProbe(cons, *kernel_);
    if (!modelOpt) {
        if (diagOn) { st << "[INT-PROBE] no model found; trying value-split hint\n"; st.flush(); }
        // Hint path: even when full enum doesn't validate a model, the
        // structural variable (highest exponent) and small-integer candidate
        // are likely SAT decisions. Emit a tautological 3-way value-split
        // lemma `(< v c) | (= v c) | (> v c)` so SAT branches on the
        // hypothesis the way nlsat's decision heuristic does. This is the
        // same pattern as stageNraSignSplit — biasing the SAT decision tree
        // without committing to the guess.
        if (registry_) {
            // Pick highest-exponent variable that hasn't been hinted yet.
            std::unordered_map<VarId, int> maxExp;
            for (const auto& c : presolveConstraints_) {
                if (c.poly == NullPoly) continue;
                auto termsOpt = kernel_->terms(c.poly);
                if (!termsOpt) continue;
                for (const auto& term : *termsOpt) {
                    for (const auto& [vid, exp] : term.powers) {
                        if (exp > maxExp[vid]) maxExp[vid] = exp;
                    }
                }
            }
            VarId pick = NullVar;
            int bestExp = 1;
            for (const auto& [v, e] : maxExp) {
                if (e <= bestExp) continue;
                if (intProbeValueSplitDone_.count(v)) continue;
                pick = v; bestExp = e;
            }
            if (pick != NullVar) {
                // Try candidate value c = 2 first (matches z3 nlsat's
                // preference on this benchmark family for high-exp vars).
                static const mpq_class kHintValue(2);
                PolyId vPoly = kernel_->mkVar(pick);
                SatLit ltL = registry_->getOrCreatePolynomialAtom(
                    vPoly, Relation::Lt, kHintValue, TheoryId::LRA);
                SatLit eqL = registry_->getOrCreatePolynomialAtom(
                    vPoly, Relation::Eq, kHintValue, TheoryId::LRA);
                SatLit gtL = registry_->getOrCreatePolynomialAtom(
                    vPoly, Relation::Gt, kHintValue, TheoryId::LRA);
                if (ltL.var != 0 && eqL.var != 0 && gtL.var != 0) {
                    TheoryLemma hint{{eqL, ltL, gtL}};
                    intProbeValueSplitDone_.insert(pick);
                    if (diagOn) {
                        st << "[INT-PROBE] HINT emitted: ("
                           << kernel_->varName(pick)
                           << " = " << kHintValue.get_str()
                           << ") | (< " << kHintValue.get_str()
                           << ") | (> " << kHintValue.get_str() << ")\n";
                        st.flush();
                    }
                    return TheoryCheckResult::mkLemma(std::move(hint));
                }
            }
        }
        return std::nullopt;
    }

    if (diagOn) {
        st << "[INT-PROBE] SAT model size=" << modelOpt->size() << "\n";
        for (const auto& [v, q] : *modelOpt) {
            st << "  " << kernel_->varName(v) << " = " << q.get_str(10) << "\n";
        }
        st.flush();
    }
    satFastModel_ = std::move(*modelOpt);
    return TheoryCheckResult::consistent();
}

// XOLVER_NRA_EQ_CASCADE — equality-cascade SAT solver (mgc-class). Assign the
// high-degree generator variables, which collapses every high-degree monomial
// (vv3^16, …) to a number and turns each residual equality linear; derive the
// remaining variables (gamma0, vv2, lambda1, mu, …) and validate the full point
// exactly via the kernel sign over ALL active constraints (invariant 1). Pure
// rational throughout — never libpoly root isolation — so it closes mgc_09/10
// where CDCAC times out projecting the degree-16/18 atom. Pure-NRA only;
// combination/N-O mode falls through (interface (dis)equalities live outside
// presolveConstraints_). SAT-only: no model found ⇒ nullopt ⇒ CDCAC/Unknown.
std::optional<TheoryCheckResult> NraSolver::stageCascade(
        TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort effort) {
    static const bool enabled = [] {
        // Promoted default-ON (#NRA-LS-E iter 2): pure-rational + exact-validated
        // over ALL active constraints (invariant 1) ⇒ sound by construction, and
        // it never invokes libpoly root isolation, so it dodges the nlsat-path
        // heap-corruption class entirely. Recovers mgc_09/mgc_10 (CDCAC times out
        // projecting their degree-16/18 atoms). Disable with XOLVER_NRA_EQ_CASCADE=0.
        const char* e = std::getenv("XOLVER_NRA_EQ_CASCADE");
        return !(e && *e == '0');
    }();
    if (!enabled) return std::nullopt;
    (void)effort;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;
    if (presolveConstraints_.empty()) return std::nullopt;

    std::vector<StructuralIntegerProbe::Constraint> cons;
    cons.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) return std::nullopt;
        cons.push_back({c.poly, c.rel});
    }

    auto modelOpt = StructuralIntegerProbe::trySolveCascade(cons, *kernel_);
    if (!modelOpt) return std::nullopt;
    satFastModel_ = std::move(*modelOpt);
    return TheoryCheckResult::consistent();
}

// Algebraic square-cascade (default ON; XOLVER_NRA_SQUARE_CASCADE=0 disables). Builds
// and EXACT-validates a Q(sqrt c) model for square-defined systems the rational
// eq-cascade can't (v^2 = non-square => algebraic root). Sound by construction:
// trySquareCascade returns true only after checking every original constraint's exact
// sign at the constructed model (invariant 1); on any inconclusive/failing check it
// returns false and we fall through to CAC/Collins unchanged.
std::optional<TheoryCheckResult> NraSolver::stageSquareCascade(
        TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort /*effort*/) {
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NRA_SQUARE_CASCADE");
        return !(e && *e == '0');
    }();
    if (!enabled) return std::nullopt;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty()) return std::nullopt;
    if (presolveConstraints_.empty()) return std::nullopt;

    std::vector<std::pair<PolyId, Relation>> cons;
    cons.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) return std::nullopt;
        cons.emplace_back(c.poly, c.rel);
    }
    std::vector<std::pair<VarId, RealValue>> model;
    if (!trySquareCascade(cons, *kernel_, &model)) return std::nullopt;
    satCacAlgModel_ = std::move(model);
    return TheoryCheckResult::consistent();
}

// XOLVER_NRA_LOCALSEARCH (Phase NRA-LS-A, default OFF). Rational-only local
// repair pre-pass. Builds the active polynomial constraint set, runs the
// NraLocalSearch WalkSAT-style search, and on a satisfying rational candidate
// exact-validates EVERY active constraint via the kernel sign (invariant 1).
// SAT only on a kernel-validated model (stored in satFastModel_); otherwise
// std::nullopt → fall to CAC / Collins. Never emits UNSAT (invariant 2).
std::optional<TheoryCheckResult> NraSolver::stageLocalSearch(
        TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort effort) {
    // Task Q: XOLVER_NRA_LOCALSEARCH promoted source-default-ON; getenv
    // guard removed (no env string in binary).
    // Per-solve ONE-SHOT at FIRST Full effort. Standard-effort firing
    // produces a candidate but subsequent cb_propagate's assertLit resets
    // satFastModel_, so the candidate never reaches cb_check_found_model.
    // At Full effort the SAT model is complete and no further assertLit
    // intervenes before getModel(); the stashed candidate survives.
    if (effort != TheoryEffort::Full) return std::nullopt;
    if (lsAttempted_) return std::nullopt;
    lsAttempted_ = true;
    // Skip in N-O combination mode: a rational satisfier of the local atom set
    // may still violate a pending interface (dis)equality. The pure-NRA path
    // catches the same cases without the soundness risk.
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;

    // Collect active polynomial constraints + var set. Bail if any active
    // constraint is non-polynomial (NullPoly); validating a witness only over
    // a subset would be unsound to report as SAT.
    std::vector<NraLocalSearch::Constraint> lsCons;
    std::set<VarId> varSet;
    lsCons.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) return std::nullopt;
        // Pull VarIds directly from the term decomposition (subtropical pattern).
        // The earlier name → getOrCreateVar round-trip MUTATED the kernel's
        // name→id table mid-solve and stalled CAC.
        auto termsOpt = kernel_->terms(c.poly);
        if (!termsOpt) return std::nullopt;
        lsCons.push_back({c.poly, c.rel, c.reason});
        for (const auto& t : *termsOpt)
            for (const auto& [v, e] : t.powers) varSet.insert(v);
    }
    if (lsCons.empty() || varSet.empty()) return std::nullopt;
    std::vector<VarId> vars(varSet.begin(), varSet.end());

    // micro-budget scaffold default (10ms) per master-spec; raise after
    // univariate boundary candidates ship.
    static const long budgetMs =
        env::paramLong("XOLVER_NRA_LS_BUDGET_MS", 10);
    static const int maxRounds =
        env::paramInt("XOLVER_NRA_LS_MAX_ROUNDS", 10);

    NraLocalSearch ls(*kernel_);
    ls.setBudgetMs(budgetMs);
    ls.setMaxRounds(maxRounds);
    const auto lsT0 = std::chrono::steady_clock::now();
    auto candOpt = ls.tryFindModel(lsCons, vars);
    const auto lsT1 = std::chrono::steady_clock::now();
    const long roundtripMs =
        std::chrono::duration_cast<std::chrono::milliseconds>(lsT1 - lsT0).count();
    lsTotalMs_ += roundtripMs;
    if (candOpt) ++lsCandidatesFound_;
    if (std::getenv("XOLVER_NRA_LS_DIAG")) {
        std::cerr << "[NRA-LS] entry vars=" << vars.size()
                  << " cons=" << lsCons.size()
                  << " candidate=" << (candOpt ? "yes" : "no") << "\n";
    }
    if (!candOpt) return std::nullopt;

    // Exact validation — every active constraint MUST hold at the rational
    // candidate under the kernel sign. The candidate is a heuristic guess;
    // never trust it (invariant 1).
    std::unordered_map<std::string, mpq_class> evalModel;
    evalModel.reserve(candOpt->size());
    for (const auto& [v, q] : *candOpt)
        evalModel.emplace(std::string(kernel_->varName(v)), q);

    for (const auto& c : presolveConstraints_) {
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
        if (!ok) return std::nullopt;   // LS lied — never report SAT.
    }

    // Sound: every active constraint exact-validates at the rational candidate.
    satFastModel_ = std::move(*candOpt);
    ++lsExactSats_;
    if (std::getenv("XOLVER_NRA_LS_DIAG")) {
        std::cerr << "[NRA-LS] SAT vars=" << vars.size()
                  << " cons=" << lsCons.size()
                  << " ms=" << lsTotalMs_ << "\n";
    }
    return TheoryCheckResult::consistent();
}

// XOLVER_NRA_CAC: conflict-driven single-cell CAC engine (the "real" CDCAC) as
// the primary NRA decision, run BEFORE the Collins buildClosure. A/B control for
// the Collins-vs-CAC differential; promotion to default is decided by that diff.
std::optional<TheoryCheckResult> NraSolver::stageCac(TheoryLemmaStorage& /*lemmaDb*/,
                                                     TheoryEffort effort) {
    if (std::getenv("XOLVER_NRA_TOWER_DIAG"))
        std::cerr << "[STAGE-CAC] entry effort=" << static_cast<int>(effort)
                  << " enableCac=" << enableCac_ << std::endl;
    if (!enableCac_) return std::nullopt;
    // EFFORT SCHEDULE (validated by the Collins-vs-CAC A/B + endorsed design):
    //   Standard effort → cheap engines (Collins as cheap CAD, linearized checks);
    //   Full effort     → the heavy CAC/Lazard hard path (this stage), then Collins
    //                     as fallback on CAC-Unknown (stageCdcac runs at all efforts).
    // So in the hybrid CAC runs ONLY at Full: it gets first refusal on the hard
    // cases Collins times out on, while Collins disposes of the easy cases cheaply
    // at Standard — running the heavy CAC at every Standard propagation instead
    // STARVES the time budget (50/150 meti-tarski timeouts in the all-efforts A/B).
    // A fair head-to-head still needs CAC at all efforts (else Collins preempts it
    // at Standard and CAC never runs) — that is what XOLVER_NRA_CAC_ONLY enables
    // (CAC at every effort + Collins disabled): CAC-only=95 vs Collins-only=64,
    // 0-unsound, confirming CAC is the stronger engine on the hard path.
    // Two orthogonal differential flags (decoupled so the full schedule matrix
    // A-E is expressible): CAC_ALL_EFFORTS runs CAC at Standard+Full (else Full
    // only); CAC_NO_COLLINS (read in stageCdcac) disables the Collins fallback.
    // NRA-COLLINS-BUDGET fix (2026-06-02): CAC_ALL_EFFORTS source-default ON.
    // Empirical: paired test 10-case meti-tarski/sqrt sample shows 10 OK / 0 TO
    // @ 1s wall vs default's 9 OK / 1 TO @ 18s. NRA reg 151/151 unchanged.
    // The legacy comment about "50/150 meti-tarski timeouts" was stale; the
    // current binary handles CAC at Standard effort efficiently. Mulligan-0004c
    // bucket recovers (Collins hangs blocked CDCAC from reaching the case).
    // Env var preserved for opt-out: XOLVER_NRA_CAC_ALL_EFFORTS=0 disables.
    static const bool cacAllEfforts = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_ALL_EFFORTS");
        if (e && *e) return *e != '0';   // explicit opt-in/opt-out
        const char* o = std::getenv("XOLVER_NRA_CAC_ONLY");   // legacy alias
        if (o && *o && *o != '0') return true;
        return true;   // source default-ON
    }();
    if (!cacAllEfforts && effort != TheoryEffort::Full) return std::nullopt;
    // COMBINATION-AWARE CAC (XOLVER_NRA_CAC_COMBINATION, default OFF — the UFNRA
    // medal lane; pairs with EQNA who owns the N-O loop). When OFF, CAC stays
    // PURE-NRA: interface (dis)equalities live in engine_ (asserted via
    // assertInterfaceEquality), not presolveConstraints_, so a CAC verdict that
    // ignored them could be wrong → defer to Collins. When ON, we instead lift
    // the interface (dis)eqs into the CAC constraint set below (root/sign-
    // preserving real constraints poly(a)-poly(b) rel 0), so CAC decides under
    // them and its UNSAT conflict carries their reason lits (see below).
    static const bool cacCombination = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_COMBINATION");
        return e && *e && *e != '0';
    }();
    if (!cacCombination &&
        (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty()))
        return std::nullopt;
#ifdef XOLVER_HAS_LIBPOLY
    // Build the constraint set + active reasons + variable order.
    std::vector<CacConstraint> cacCons;
    std::vector<SatLit> activeReasons;
    std::set<VarId> varSet;
    cacCons.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) return std::nullopt;          // non-polynomial ⇒ defer to Collins
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) return std::nullopt;
        for (VarId v : rp->variables()) varSet.insert(v);
        cacCons.push_back({std::move(*rp), c.rel});
        activeReasons.push_back(c.reason);
    }
    // Combination: lift each N-O interface (dis)equality into a CAC constraint,
    // keeping its reason lit aligned in activeReasons (index ⇒ reason). The
    // conversion REUSES the exact path assertInterfaceEquality fed to engine_
    // (PolynomialConverter::convertConstraint → cc.diff rel 0). If a shared term
    // is not NRA-poly-expressible (UF app feeding a real var) → DEFER the whole
    // CAC run to Collins (sound floor: engine_ already has the interface
    // constraints). The unsatCore (origins) machinery then makes the combination
    // conflict include exactly the interface lits that participated.
    if (cacCombination) {
        auto liftIface = [&](const std::vector<InterfaceEq>& ifaces, Relation rel) -> bool {
            for (const auto& e : ifaces) {
                if (!sharedTermRegistry_ || !coreIr_ || !converter_) return false;
                const auto* stA = sharedTermRegistry_->get(e.a);
                const auto* stB = sharedTermRegistry_->get(e.b);
                if (!stA || !stB) return false;
                auto cc = converter_->convertConstraint(stA->coreExpr, stB->coreExpr, rel, *coreIr_);
                if (cc.status == PolyConstraintStatus::Tautology) continue;   // adds nothing
                if (cc.status == PolyConstraintStatus::Conflict) return false; // constant clash → defer (engine_ caught it at assert)
                if (!cc.isConstraint()) return false;                         // not poly-expressible → defer
                auto rp = RationalPolynomial::fromPolyId(cc.diff, *kernel_);
                if (!rp) return false;
                for (VarId v : rp->variables()) varSet.insert(v);
                cacCons.push_back({std::move(*rp), rel});
                activeReasons.push_back(e.reason);
            }
            return true;
        };
        if (!liftIface(interfaceEqualities_, Relation::Eq) ||
            !liftIface(interfaceDisequalities_, Relation::Neq))
            return std::nullopt;   // shared term not poly-expressible ⇒ sound defer to Collins
    }

    // ====================================================================
    // Phase C-2: NLA-cuts hook (XOLVER_NRA_NLA_CUTS, default-OFF).
    //
    // Append redundant tightening cuts (monotonicity-square + monotonicity-
    // product + McCormick bilinear envelope) derived from single-variable
    // bound constraints currently in presolveConstraints_. Each cut is a
    // logical implication of its source bounds, so adding it to cacCons is
    // sat/unsat preserving — it can only speed CAC projection, never change
    // the answer.
    //
    // SOUNDNESS GATE this commit pins:
    //   Only single-reason cuts are injected. The cacCons / activeReasons
    //   parallel-index contract assumes one SatLit per constraint; a cut
    //   with two reasons would need a synthetic conjunction lit or
    //   multi-reason aggregation in conflict generation (deferred to a
    //   later Phase C-3 commit). Until that lands, multi-reason cuts are
    //   silently dropped here.
    //
    // The bound-extraction scans presolveConstraints_ for single-variable
    // linear atoms `c1*v + c0 rel 0` (constant + linear-in-one-var), maps
    // each to a (var → lo/hi) update on the constructed interval, then
    // feeds the result into NlaCutsRunner.
    // ====================================================================
    static const bool nlaCutsEnabled = [] {
        const char* e = std::getenv("XOLVER_NRA_NLA_CUTS");
        return e && *e && *e != '0';
    }();
    if (nlaCutsEnabled) {
        // Single-pass single-var bound extraction. For each constraint
        // poly = c0 (constant) + c1*v (single var, degree 1, no other
        // terms), derive lo/hi on v from the relation.
        std::map<VarId, nla::VarInterval> intervalMap;
        for (const auto& c : presolveConstraints_) {
            if (c.poly == NullPoly) continue;
            auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
            if (!rp) continue;
            // Must be: at most one variable, and that variable degree 1.
            auto vars = rp->variables();
            if (vars.size() != 1) continue;
            VarId v = *vars.begin();
            if (rp->degree(v) != 1) continue;
            // Extract c0 (constant) + c1 (coefficient of v^1).
            auto coeffs = rp->coefficients(v);  // [const, linear-coeff, ...]
            if (coeffs.size() != 2) continue;
            if (!coeffs[0].isConstant() || !coeffs[1].isConstant()) continue;
            mpq_class c0 = coeffs[0].constantValue();
            mpq_class c1 = coeffs[1].constantValue();
            if (c1 == 0) continue;
            // Solve `c0 + c1*v rel 0` for v: bound = -c0/c1, direction
            // flips when c1 < 0.
            mpq_class bound = -c0 / c1;
            Relation effRel = c.rel;
            if (c1 < 0) {
                // Multiplying inequality by negative flips direction.
                switch (effRel) {
                    case Relation::Leq: effRel = Relation::Geq; break;
                    case Relation::Geq: effRel = Relation::Leq; break;
                    case Relation::Lt:  effRel = Relation::Gt;  break;
                    case Relation::Gt:  effRel = Relation::Lt;  break;
                    case Relation::Eq:  case Relation::Neq: break;  // unchanged
                }
            }
            // Map to lo / hi update on intervalMap[v]. We accept Leq/Geq/Eq;
            // Lt/Gt would need strict-vs-non-strict handling which the NLA
            // monotonicity rules don't require (the cut math is sound for
            // non-strict bounds anyway).
            auto& vi = intervalMap[v];
            if (vi.varPoly == NullPoly) vi.varPoly = kernel_->mkVar(v);
            auto tighter = [](std::optional<mpq_class>& lo,
                              std::optional<mpq_class>& hi,
                              const mpq_class& val, Relation r) {
                switch (r) {
                    case Relation::Leq: case Relation::Lt:
                        if (!hi || val < *hi) hi = val;
                        break;
                    case Relation::Geq: case Relation::Gt:
                        if (!lo || val > *lo) lo = val;
                        break;
                    case Relation::Eq:
                        if (!lo || val > *lo) lo = val;
                        if (!hi || val < *hi) hi = val;
                        break;
                    case Relation::Neq: break;
                }
            };
            // Track reason: only single-reason cuts will be injected, so
            // attach c.reason to the interval whose bound this constraint
            // tightens. The runner unions reasons; when a generator method
            // produces a cut from this interval alone (monotonicitySquare),
            // it inherits this one reason — sound and single-reason.
            // For pair cuts (monotonicityProduct, mccormickBilinear) we'll
            // see N reasons in the cut and drop it below.
            tighter(vi.lo, vi.hi, bound, effRel);
            // Reason aggregation: keep the LAST single-bound reason. For
            // monotonicitySquare on this var, the cut will list just this
            // one reason — the precondition we need for the single-reason
            // injection guard below.
            vi.reasons = {c.reason};
        }
        std::vector<nla::VarInterval> intervals;
        intervals.reserve(intervalMap.size());
        for (auto& [v, vi] : intervalMap) intervals.push_back(std::move(vi));

        nla::NlaCutsRunner runner(*kernel_);
        // maxPairs = 0: skip product / McCormick (multi-reason); for Phase
        // C-2 we only inject square cuts which are single-reason.
        auto cuts = runner.runShapeCuts(intervals, /*maxPairs=*/0);
        for (const auto& cut : cuts) {
            if (cut.poly == NullPoly) continue;
            if (cut.reasons.size() != 1) continue;  // see soundness gate above
            auto rp = RationalPolynomial::fromPolyId(cut.poly, *kernel_);
            if (!rp) continue;
            for (VarId v : rp->variables()) varSet.insert(v);
            cacCons.push_back({std::move(*rp), cut.rel});
            activeReasons.push_back(cut.reasons[0]);
        }
    }

    if (cacCons.empty() || varSet.empty()) return std::nullopt;
    std::vector<VarId> varOrder(varSet.begin(), varSet.end());  // sorted (std::set)

    // Track C round 4 #51: variable-order heuristic. Brown-McCallum-style
    // simplified: for each var compute (maxDeg, occCount) across cacCons; sort
    // varOrder ascending by (deg, occ) so low-info vars project out first
    // (outer), keeping high-degree vars as the lifting base (inner). Tiebreaker:
    // source VarId (stable, reproducible). Soundness: variable order does not
    // affect CDCAC completeness — it cannot introduce unsoundness, only shift
    // perf. Gated XOLVER_NRA_CAC_VAR_ORDER, default OFF.
    static const bool varOrderHeuristic = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_VAR_ORDER");
        return e && *e && *e != '0';
    }();
    if (varOrderHeuristic && varOrder.size() > 1) {
        std::unordered_map<VarId, std::pair<int, int>> scores;   // var -> (maxDeg, occCount)
        scores.reserve(varOrder.size());
        for (VarId v : varOrder) scores[v] = {0, 0};
        for (const auto& c : cacCons) {
            for (VarId v : c.poly.variables()) {
                auto it = scores.find(v);
                if (it == scores.end()) continue;
                const int d = c.poly.degree(v);
                if (d > it->second.first) it->second.first = d;
                ++it->second.second;
            }
        }
        // XOLVER_NRA_CAC_VAR_ORDER_DIR: "asc" (default, classic Collins —
        // low-degree first) or "desc" (high-degree first — matches z3-nlsat
        // decision heuristic; needed for SAT-sample sweep to hit structural
        // vars like vv3^9 at level 0 instead of being projected last).
        static const bool descOrder = [] {
            const char* e = std::getenv("XOLVER_NRA_CAC_VAR_ORDER_DESC");
            return e && *e && *e != '0';
        }();
        std::sort(varOrder.begin(), varOrder.end(), [&](VarId a, VarId b) {
            const auto& sa = scores[a];
            const auto& sb = scores[b];
            if (sa.first != sb.first) {
                return descOrder ? (sa.first > sb.first) : (sa.first < sb.first);
            }
            if (sa.second != sb.second) {
                return descOrder ? (sa.second > sb.second) : (sa.second < sb.second);
            }
            return a < b;   // stable tiebreaker on source VarId
        });
    }

    if (!cacBackend_) cacBackend_ = std::make_unique<LibpolyBackend>(kernel_.get());
    // Wall-clock deadline: in the HYBRID (Collins fallback present) bound CAC@Full
    // to a time-share so a hard covering YIELDS to Collins (Unknown→fallback)
    // rather than grinding to the global timeout and starving it. When CAC is the
    // SOLE engine (XOLVER_NRA_CAC_NO_COLLINS / _ONLY) leave it unbounded (0) and
    // rely on the external timeout. Override via XOLVER_NRA_CAC_DEADLINE_MS.
    static const bool soleEngine = [] {
        const char* n = std::getenv("XOLVER_NRA_CAC_NO_COLLINS");
        const char* o = std::getenv("XOLVER_NRA_CAC_ONLY");
        return (n && *n && *n != '0') || (o && *o && *o != '0');
    }();
    // hybrid default: 2s CAC@Full share (2s-beats-60s: a hard covering yields
    // fast to Collins instead of grinding); rest of 1200s is Collins.
    static const long cacDeadlineMs =
        env::paramLong("XOLVER_NRA_CAC_DEADLINE_MS", 2000);
    static const bool earlyInfeas = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_EARLY_INFEAS");
        return e && *e && *e != '0';
    }();
    static const bool pruneIntervals = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_PRUNE_INTERVALS");
        return e && *e && *e != '0';
    }();
    static const bool earlyInfeasSafe = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_EARLY_INFEAS_SAFE");
        return e && *e && *e != '0';
    }();
    const bool inloopPrune = true;  // promoted default-ON
    CacEngine::Config cfg;
    // Scale CAC's deadline to ~1/4 of the wall-clock remaining when
    // XOLVER_WALLCLOCK_SCALE is on (else == cacDeadlineMs). Lets CAC keep
    // working when the competition timeout leaves time, instead of yielding
    // to Collins at a flat 2s and then idling.
    cfg.deadlineMillis = soleEngine ? 0 : wall::scaledBudgetMs(cacDeadlineMs, 1, 4);
    cfg.earlyInfeas = earlyInfeas;
    cfg.pruneIntervals = pruneIntervals;
    cfg.earlyInfeasSafe = earlyInfeasSafe;
    cfg.inloopPrune = inloopPrune;
    // #63 Phase C2: keep a copy of cacCons for the rational-fallback validator.
    // (CacEngine std::move's the constraint vector below, leaving cacCons empty.)
    std::vector<CacConstraint> consCopy = cacCons;
    CacEngine eng(cacBackend_.get(), kernel_.get(), varOrder, std::move(cacCons), cfg);
    CacResult res = eng.solve();

    const bool diag = std::getenv("XOLVER_NRA_CAC_DIAG") != nullptr;
    if (diag) {
        std::ofstream st("/tmp/cac_diff.txt", std::ios::app);
        st << "[CAC] vars=" << varOrder.size() << " cons=" << presolveConstraints_.size()
           << " verdict=" << (res.status == CacStatus::Sat ? "sat"
                              : res.status == CacStatus::Unsat ? "unsat" : "unknown")
           << " depth=" << eng.maxDepthReached()
           << (res.status == CacStatus::Unknown ? (" reason=" + eng.lastUnknown()) : std::string())
           << "\n";
        st.flush();
    }

    if (res.status == CacStatus::Unsat) {
        // CAC-UNSAT is trusted (promoted default-ON). The per-cell certification
        // / required-coefficients characterization fix that closed the earlier
        // false-UNSAT class (sat cases nra_014/022/047/138) was validated by the
        // two-round full-corpus differential (0 wrong answers). CAC's covering
        // conflict is returned as the theory conflict below; its validated-SAT
        // path remains sound and is returned as before.
        TheoryConflict conflict;
        // CONFLICT MINIMIZATION (XOLVER_NRA_CAC_MIN_CONFLICT, default OFF): use
        // only the reason lits of the constraints that actually delineated the
        // covering (CacResult::unsatCore) instead of the whole asserted set.
        // The sub-conjunction over those constraints is itself UNSAT (the covering
        // proves it), so the learned lemma is sound and much tighter — less SAT-
        // core churn. unsatCore is a conservative superset of the minimal core;
        // an EMPTY core (could-not-attribute) falls back to all reasons (sound).
        // This is ALSO the mechanism the combination conflict will reuse to carry
        // the interface-(dis)eq lits that participated (see CAC.md / task P5).
        static const bool minConflict = [] {
            const char* e = std::getenv("XOLVER_NRA_CAC_MIN_CONFLICT");
            return e && *e && *e != '0';
        }();
        if (minConflict && !res.unsatCore.empty()) {
            std::vector<SatLit> minimized;
            minimized.reserve(res.unsatCore.size());
            for (size_t idx : res.unsatCore)
                if (idx < activeReasons.size()) minimized.push_back(activeReasons[idx]);
            if (!minimized.empty()) conflict.clause = std::move(minimized);
            else conflict.clause = std::move(activeReasons);   // defensive fallback
        } else {
            conflict.clause = std::move(activeReasons);
        }
        return TheoryCheckResult::mkConflict(std::move(conflict));
    }
    if (res.status == CacStatus::Sat) {
        // COMBINATION (#43): a CAC SAT under interface constraints means NRA is
        // consistent with the asserted (dis)eqs. With XOLVER_NRA_CAC_COMB_SAT
        // ON, getDeducedSharedEqualities() emits the pairwise shared-term
        // equalities the model implies, so the combination loop can build the
        // arrangement directly. With it OFF (default), defer to Collins as
        // before (the v1 conservative path).
        static const bool combSatHere = [] {
            const char* e = std::getenv("XOLVER_NRA_CAC_COMB_SAT");
            return e && *e && *e != '0';
        }();
        if (!combSatHere && cacCombination &&
            (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty()))
            return std::nullopt;
        // Phase B (#55, XOLVER_NRA_CAC_SAT_ALGEBRAIC default OFF): accept
        // CAC SAT models with algebraic values. CAC's engine validated
        // allHold via exact signAt before returning SAT (existing invariant
        // 1); the model — rational or algebraic — is a genuine satisfier of
        // every constraint. Pre-#55 the algebraic case was deferred to
        // Collins, which timed out on the meti-tarski/sqrt cluster (4 of 5
        // sample cases had CAC verdict=sat repeatedly dropped here).
        static const bool acceptAlgebraic = [] {
            const char* e = std::getenv("XOLVER_NRA_CAC_SAT_ALGEBRAIC");
            return e && *e && *e != '0';
        }();
        bool anyAlgebraic = false;
        for (size_t i = 0; i < res.model.values.size(); ++i) {
            if (!res.model.values[i].isRational()) { anyAlgebraic = true; break; }
        }
        if (anyAlgebraic && !acceptAlgebraic) return std::nullopt;
        if (!anyAlgebraic) {
            std::unordered_map<VarId, mpq_class> rationalModel;
            for (size_t i = 0; i < res.model.values.size(); ++i)
                rationalModel.emplace(res.model.varOrder[i], res.model.values[i].rational);
            satFastModel_ = std::move(rationalModel);
        } else {
            // Algebraic channel: keep the full typed value (rational or
            // RealAlg) for getModel to surface to ArithModelValidator and
            // the printed-model channel.
            std::vector<std::pair<VarId, RealValue>> alg;
            alg.reserve(res.model.values.size());
            for (size_t i = 0; i < res.model.values.size(); ++i) {
                const auto& v = res.model.values[i];
                if (v.isRational()) {
                    alg.emplace_back(res.model.varOrder[i], RealValue::fromMpq(v.rational));
                } else {
                    // RealAlg → RealValue: mirror CdcacSolver::sampleValueToRealValue.
                    // The backend stores coefficients high-to-low; AlgebraicNumber
                    // wants low-to-high. Degenerate (no defining poly) → rational
                    // midpoint of the isolating interval (fallback).
                    RealValue rv;
                    if (cacBackend_ && v.root.definingPoly != NullUniPolyId) {
                        const auto& hiToLo = cacBackend_->getUni(v.root.definingPoly);
                        AlgebraicNumber an;
                        an.coefficients.assign(hiToLo.rbegin(), hiToLo.rend());
                        an.lower = v.root.lower;
                        an.upper = v.root.upper;
                        an.lowerOpen = true;
                        an.upperOpen = true;
                        rv = RealValue::fromAlgebraic(std::move(an));
                    } else {
                        const mpq_class mid = (v.root.lower + v.root.upper) / 2;
                        rv = RealValue::fromMpq(mid);
                    }
                    alg.emplace_back(res.model.varOrder[i], std::move(rv));
                }
            }
            satCacAlgModel_ = std::move(alg);
        }
        return TheoryCheckResult::consistent();
    }
    // #63 Phase C2 follow-on: when CAC bails on `leaf-atom-unsupported` with a
    // captured failing sample, attempt a rational-fallback retry. Replace each
    // algebraic coord with its isolating-interval midpoint, then EXACT-sign-
    // check every active CAC constraint at the rational sample. If ALL hold,
    // the rational sample is a genuine satisfier — invariant 1: this is an
    // exact-validated SAT, not a CAC-projected one. UNSAT verdicts from the
    // rational system are NEVER returned (could be false-UNSAT since rounding
    // algebraic to midpoint can miss the true satisfier); only sat is taken.
    // The cluster-wide diagnostic shows 100% of atan/CMOS timeouts and 96% of
    // exp timeouts hit this exact failure mode (see Phase C2 docs).
    static const bool rationalFallback = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_RATIONAL_FALLBACK");
        return e && *e && *e != '0';
    }();
    if (rationalFallback &&
        res.status == CacStatus::Unknown &&
        !res.unknownSample.varOrder.empty() &&
        res.unknownSample.varOrder.size() == res.unknownSample.values.size()) {

        // Build the set of candidate rational values for each var. For a rational
        // sample value, the single value. For an algebraic value (root in (lo, hi)),
        // probe at three offsets: lo + 1/4 * (hi-lo), 1/2 * (hi+lo), hi - 1/4 * (hi-lo)
        // — covering both sides of the algebraic root so a sign-flipping constraint
        // has a positive chance of being satisfied at one of the probes.
        const size_t N = res.unknownSample.varOrder.size();
        std::vector<std::vector<mpq_class>> candidates(N);
        for (size_t i = 0; i < N; ++i) {
            const auto& v = res.unknownSample.values[i];
            if (v.isRational()) {
                candidates[i].push_back(v.rational);
            } else {
                const mpq_class width = v.root.upper - v.root.lower;
                candidates[i].push_back(v.root.lower + width / 4);
                candidates[i].push_back(v.root.lower + width / 2);
                candidates[i].push_back(v.root.upper - width / 4);
            }
        }

        // Cap the cartesian product enumeration: at most 3^4 = 81 probes; for >4
        // algebraic vars use midpoints only (1 probe).
        size_t totalProbes = 1;
        for (const auto& c : candidates) totalProbes *= c.size();
        if (totalProbes > 81) {
            for (size_t i = 0; i < N; ++i) {
                if (candidates[i].size() > 1) candidates[i] = {candidates[i][1]};  // mid only
            }
            totalProbes = 1;
        }

        bool found = false;
        SamplePoint chosen;
        std::vector<size_t> idx(N, 0);
        for (size_t probe = 0; probe < totalProbes; ++probe) {
            SamplePoint ratSample;
            for (size_t i = 0; i < N; ++i) {
                ratSample.push(res.unknownSample.varOrder[i],
                               RealAlg::fromRational(candidates[i][idx[i]]));
            }
            bool allHold = true;
            for (const auto& c : consCopy) {
                auto norm = c.poly.toPrimitiveInteger(*kernel_);
                if (!norm.ok()) { allHold = false; break; }
                const Sign s = cacBackend_->signAt(norm.poly, ratSample);
                if (s == Sign::Unknown || !relationHolds(s, c.rel)) {
                    allHold = false;
                    break;
                }
            }
            if (allHold) {
                chosen = std::move(ratSample);
                found = true;
                break;
            }
            // increment idx (rightmost-first odometer)
            for (size_t pos = 0; pos < N; ++pos) {
                if (++idx[pos] < candidates[pos].size()) break;
                idx[pos] = 0;
            }
        }
        if (found) {
            std::unordered_map<VarId, mpq_class> rationalModel;
            for (size_t i = 0; i < chosen.varOrder.size(); ++i) {
                rationalModel.emplace(chosen.varOrder[i],
                                      chosen.values[i].rational);
            }
            satFastModel_ = std::move(rationalModel);
            return TheoryCheckResult::consistent();
        }
    }
#endif
    return std::nullopt;  // Unknown / no libpoly ⇒ fall through to Collins
}

// Stage 2: the CDCAC (Collins) engine. Always yields a definite verdict.
std::optional<TheoryCheckResult> NraSolver::stageCdcac(TheoryLemmaStorage& /*lemmaDb*/,
                                                       TheoryEffort /*effort*/) {
    if (std::getenv("XOLVER_NRA_TOWER_DIAG"))
        std::cerr << "[STAGE-CDCAC] reached (engine_ will run core_->solve)" << std::endl;
    // XOLVER_NRA_CAC_NO_COLLINS (differential): disable the Collins fallback so
    // CAC is the sole engine. Return Unknown (not nullopt) so the solver reports
    // unknown when CAC cannot decide, rather than a default/false verdict.
    static const bool noCollins = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_NO_COLLINS");
        if (e && *e && *e != '0') return true;
        const char* o = std::getenv("XOLVER_NRA_CAC_ONLY");   // legacy alias = all-efforts + no-collins
        return o && *o && *o != '0';
    }();
    if (noCollins) return TheoryCheckResult::unknown("cac-only-collins-disabled");
    return engine_.check();
}

// XOLVER_NRA_LINEARIZE incremental-linearization SAT LOOP (default OFF).
//
// Closes the linearization SAT loop for NRA (mirrors NiaSolver but for reals):
//
//   1. Read the LRA sibling's candidate relaxation model (numericAssignments).
//   2. VALIDATE it exactly: for every active original constraint (linear AND
//      nonlinear) compute the exact kernel sign at that rational point and
//      check the relation holds. If the model is non-empty and ALL hold, the
//      candidate is a genuine NRA model → return consistent() (invariant 1:
//      the verdict is backed by an exact-kernel check, never by the
//      abstraction alone).
//   3. Else REFINE: mirror active linear bounds + emit McCormick/square cuts
//      tangent at the CURRENT model point (model-construction), into lemmaDb.
//   4. LOOP CONTROL: if new cuts were emitted, return ONE as mkLemma (the rest
//      sit in lemmaDb). A Lemma result stops the pipeline BEFORE stageCdcac and
//      the SAT core adds the clause + re-solves, re-invoking the theory next
//      round (contract verified: ArithSolverBase::runReasonerPipeline returns
//      the first non-nullopt; CadicalTheoryPropagator enqueues the lemma clause
//      and re-solves). If the round cap is hit or no new cuts were generated
//      (dedup exhausted) and the model didn't validate, fall through to CDCAC.
//
// All diagnostics go to /tmp/linprobe.txt (CLI stderr is suppressed on the
// worker thread). CDCAC remains the backstop for everything this loop can't
// close. Flag OFF → returns nullopt immediately, identical to before.
std::optional<TheoryCheckResult> NraSolver::stageLinearizeProbe(TheoryLemmaStorage& lemmaDb,
                                                                TheoryEffort /*effort*/) {
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NRA_LINEARIZE");
        return e && (e[0]=='1'||e[0]=='t'||e[0]=='T'||e[0]=='y'||e[0]=='Y');
    }();
    if (!enabled) return std::nullopt;
    if (!registry_ || !linAdapter_) return std::nullopt;

    static const int kRefineCap = [] {
        int v = env::paramInt("XOLVER_NRA_LINEARIZE_CAP", 60);
        return v > 0 ? v : 60;
    }();

    std::ofstream lp("/tmp/linprobe.txt", std::ios::app);

    // Total degree of a polynomial via its monomial decomposition. Returns -1 if
    // the kernel cannot decompose it (e.g. non-integer coefficients).
    auto totalDegree = [&](PolyId p) -> int {
        auto termsOpt = kernel_->terms(p);
        if (!termsOpt) return -1;
        int maxDeg = 0;
        for (const auto& t : *termsOpt) {
            int d = 0;
            for (const auto& pe : t.powers) d += pe.second;
            if (d > maxDeg) maxDeg = d;
        }
        return maxDeg;
    };

    // --- Step 1: read the LRA sibling's candidate relaxation model. ----------
    std::unordered_map<std::string, mpq_class> model;
    bool modelFilled = false;
    if (linearSibling_) {
        auto m = linearSibling_->getModel();
        if (m) {
            for (const auto& [name, rv] : m->numericAssignments) {
                auto q = rv.tryAsRational();
                if (q) model.emplace(name, *q);  // skip algebraic/non-rational
            }
            modelFilled = !model.empty();
        }
    }
    // Diagnostic fingerprint of the BASE (non-aux) var values, to tell whether
    // the candidate model changes across rounds or the loop is stuck.
    mpq_class fp(0);
    int nBase = 0, nNonzeroBase = 0;
    for (const auto& [name, val] : model) {
        if (name.rfind("__nl_aux_", 0) == 0) continue;
        ++nBase;
        if (val != 0) ++nNonzeroBase;
        fp += val * val + val;  // order-independent-ish mix
    }
    if (std::getenv("XOLVER_NRA_LINEARIZE_DUMP") && modelFilled) {
        std::ofstream md("/tmp/linmodel.txt", std::ios::app);
        md << "--- model (nBase=" << nBase << " nNonzeroBase=" << nNonzeroBase
           << " total=" << model.size() << ") ---\n";
        int shown = 0;
        for (const auto& [name, val] : model) {
            if (shown++ >= 40) { md << "...\n"; break; }
            md << "  " << name << " = " << val.get_str() << "\n";
        }
        md.flush();
    }

    // --- Step 2: exact validation of EVERY active original constraint. -------
    // The kernel sgn() requires a COMPLETE assignment (every variable of the
    // polynomial must be present, else libpoly evaluates a non-constant value
    // and the rational-interval path corrupts the heap). Vars absent from the
    // candidate model are treated as 0 for the sign check (validation fallback)
    // by explicitly 0-filling each polynomial's variables. The check is over
    // the rational kernel sign, so a pass is a sound NRA model.
    int validated = 0, total = 0;
    bool allHold = true;
    {
        for (const auto& c : presolveConstraints_) {
            if (c.poly == NullPoly) continue;  // non-polynomial placeholder
            ++total;
            std::unordered_map<std::string, mpq_class> evalModel = model;
            for (const auto& vn : kernel_->variables(c.poly)) {
                evalModel.emplace(vn, mpq_class(0));  // 0-fill absent vars
            }
            int s = kernel_->sgn(c.poly, evalModel);
            bool ok = false;
            switch (c.rel) {
                case Relation::Eq:  ok = (s == 0); break;
                case Relation::Geq: ok = (s >= 0); break;
                case Relation::Leq: ok = (s <= 0); break;
                case Relation::Gt:  ok = (s > 0);  break;
                case Relation::Lt:  ok = (s < 0);  break;
                case Relation::Neq: ok = (s != 0); break;
            }
            if (ok) ++validated;
            else allHold = false;
        }
    }

    if (modelFilled && total > 0 && allHold) {
        lp << "[LINPROBE] round=" << linRefineRound_ << " model=filled"
           << " validated=" << validated << "/" << total
           << " newcuts=0 action=SAT\n";
        lp.flush();
        // Sound: the exact kernel sign validates ALL original constraints at a
        // concrete rational point. consistent() = SAT, stop the pipeline.
        return TheoryCheckResult::consistent();
    }

    // --- Step 3: refine. Mirror linear bounds + emit model-tangent cuts. -----
    std::vector<TheoryLemma> newLemmas;

    {
        std::vector<GenericActiveAssignment> gaas;
        gaas.reserve(activeRecords_.size());
        for (const auto& r : activeRecords_) {
            gaas.push_back({r.lit, r.atom, r.value});
        }
        auto mirrorLemmas = linAdapter_->mirrorActiveLinearBounds(gaas, TheoryId::LRA);
        for (auto& ml : mirrorLemmas) {
            if (!lemmaDb.contains(ml)) {
                lemmaDb.insertIfNew(ml);
                newLemmas.push_back(std::move(ml));
            }
        }
    }

    std::vector<ActiveNiaConstraint> activeNonlinear;
    for (const auto& pc : presolveConstraints_) {
        if (pc.poly == NullPoly) continue;
        if (totalDegree(pc.poly) < 2) continue;   // linear: already mirrored above
        activeNonlinear.push_back({pc.poly, pc.rel, pc.reason});
    }

    // Phase 4 (XOLVER_NRA_NLEXT_TANGENT_PERTURB): detect stuck-model. The
    // refinement loop is "stuck" when (a) the candidate-model fingerprint is
    // unchanged from the previous round AND (b) the previous round produced
    // zero NEW cuts (every cut was already in the cache). In that situation
    // every additional refinement at the same tangent point will keep hitting
    // the cache, and we converge to no progress. Perturbing the tangent point
    // breaks the loop by introducing fresh cuts at NEW points; convex tangent
    // is sound at any point, so this is safe.
    static const bool perturbEnabled = [] {
        const char* e = std::getenv("XOLVER_NRA_NLEXT_TANGENT_PERTURB");
        return e && (e[0]=='1'||e[0]=='t'||e[0]=='T'||e[0]=='y'||e[0]=='Y');
    }();
    // Cap perturbations per solve. Each perturbation injects fresh
    // tangent cuts that may extend the refinement loop without
    // converging; cap at a small number so we eventually fall through
    // to CDCAC rather than spinning. nra_150 regression analysis:
    // unbounded perturbation extended LIN refinement past its natural
    // termination on a SAT case, never reaching validator.
    static const int kPerturbCap = [] {
        int v = env::paramInt("XOLVER_NRA_NLEXT_TANGENT_PERTURB_CAP", 4);
        return v >= 0 ? v : 4;
    }();
    // Only activate perturbation AFTER the natural refinement loop has
    // had time to converge on its own. Earlier-round stuck states usually
    // resolve once McCormick/SquareCut emits its second-round refinement;
    // perturbation early disturbs SAT cases that would have validated in
    // a few more rounds (nra_150_sat regression analysis).
    static const int kPerturbMinRound = [] {
        // default 30 = half of default kRefineCap=60
        int v = env::paramInt("XOLVER_NRA_NLEXT_TANGENT_PERTURB_MINROUND", 30);
        return v >= 0 ? v : 30;
    }();
    bool isStuck = perturbEnabled && modelFilled &&
                   linRefineRound_ >= kPerturbMinRound &&
                   fp == lastLinFp_ && linLastNewCuts_ == 0 &&
                   static_cast<int>(linPerturbSeed_) < kPerturbCap;
    if (isStuck) {
        ++linStuckRounds_;
    } else {
        linStuckRounds_ = 0;
    }
    lastLinFp_ = fp;

    // Build the model passed to the linearizer. When stuck, perturb ONE
    // variable per round (round-robin via linPerturbSeed_) to a "diverse
    // seed" value. The pool of seed offsets is small and bounded:
    //   +1, -1, 0, +2, -2, model + small step, model - small step
    std::unordered_map<std::string, mpq_class> linModel = model;
    if (isStuck && !linModel.empty()) {
        std::vector<std::string> baseVars;
        baseVars.reserve(linModel.size());
        for (const auto& [name, _] : linModel)
            if (name.rfind("__nl_aux_", 0) != 0) baseVars.push_back(name);
        if (!baseVars.empty()) {
            std::sort(baseVars.begin(), baseVars.end()); // deterministic order
            uint32_t vIdx = linPerturbSeed_ % baseVars.size();
            uint32_t offIdx = (linPerturbSeed_ / baseVars.size()) % 7;
            const std::string& vn = baseVars[vIdx];
            const mpq_class& cur = linModel.at(vn);
            mpq_class perturbed;
            switch (offIdx) {
                case 0: perturbed = cur + 1; break;
                case 1: perturbed = cur - 1; break;
                case 2: perturbed = mpq_class(0); break;
                case 3: perturbed = cur + 2; break;
                case 4: perturbed = cur - 2; break;
                case 5: perturbed = cur + mpq_class(1, 2); break;   // +1/2
                case 6: perturbed = cur - mpq_class(1, 2); break;
                default: perturbed = cur;
            }
            linModel[vn] = perturbed;
            ++linPerturbSeed_;
        }
    }

    int nNonlinearNormalized = 0;
    if (!activeNonlinear.empty()) {
        NiaNormalizer normalizer(*kernel_);
        auto normalizedOpt = normalizer.normalize(activeNonlinear);
        if (normalizedOpt) {
            nNonlinearNormalized = static_cast<int>(normalizedOpt->size());
            // Tangent the cuts at the CURRENT (possibly perturbed) model point.
            // When the sibling has no model yet, fall back to the sign-bounded
            // linearizer (positivity assertions derive one-sided bounds → Family
            // 0 sign-only cuts fire) instead of the empty-bound path which
            // emitted ZERO sign cuts for sign-pinned mgc-class formulas.
            std::unordered_map<std::string, int> signMap;
            for (const auto& c : presolveConstraints_) {
                if (c.poly == NullPoly) continue;
                if (c.rel != Relation::Lt && c.rel != Relation::Leq &&
                    c.rel != Relation::Gt && c.rel != Relation::Geq) continue;
                auto termsOpt = kernel_->terms(c.poly);
                if (!termsOpt || termsOpt->size() != 1) continue;
                const auto& t = (*termsOpt)[0];
                if (t.powers.size() != 1 || t.powers[0].second != 1) continue;
                std::string vn = std::string(kernel_->varName(t.powers[0].first));
                int sign = 0;
                if (c.rel == Relation::Lt && t.coefficient < 0) sign = 1;
                else if (c.rel == Relation::Leq && t.coefficient < 0) sign = 1;
                else if (c.rel == Relation::Gt && t.coefficient > 0) sign = 1;
                else if (c.rel == Relation::Geq && t.coefficient > 0) sign = 1;
                else if (c.rel == Relation::Lt && t.coefficient > 0) sign = -1;
                else if (c.rel == Relation::Leq && t.coefficient > 0) sign = -1;
                else if (c.rel == Relation::Gt && t.coefficient < 0) sign = -1;
                else if (c.rel == Relation::Geq && t.coefficient < 0) sign = -1;
                if (sign != 0) signMap[vn] = sign;
            }
            auto lr = modelFilled
                ? linAdapter_->runLinearizerAtModel(*normalizedOpt, linModel, lemmaDb)
                : (signMap.empty()
                    ? linAdapter_->runLinearizer(*normalizedOpt, lemmaDb)
                    : linAdapter_->runLinearizerWithSignBounds(*normalizedOpt, signMap, lemmaDb));
            if (lr.status == LinearizationStatus::Lemma) {
                for (auto& item : lr.lemmas) {
                    if (!lemmaDb.contains(item.lemma)) {
                        lemmaDb.insertIfNew(item.lemma);
                        newLemmas.push_back(item.lemma);
                        if (item.cacheKey) linAdapter_->markEmitted(*item.cacheKey);
                    }
                }
            }
        }
    }

    int nNewCuts = static_cast<int>(newLemmas.size());
    linLastNewCuts_ = nNewCuts;  // Phase 4: feed into next-round stuck detection.

    // --- Step 4: loop control. -----------------------------------------------
    if (nNewCuts > 0 && linRefineRound_ < kRefineCap) {
        ++linRefineRound_;
        lp << "[LINPROBE] round=" << linRefineRound_
           << " model=" << (modelFilled ? "filled" : "empty")
           << " validated=" << validated << "/" << total
           << " nonlinearNormalized=" << nNonlinearNormalized
           << " newcuts=" << nNewCuts << " fp=" << fp.get_str() << " action=REFINE\n";
        lp.flush();
        // Return ONE lemma; the rest sit in lemmaDb. A Lemma stops the pipeline
        // before stageCdcac and forces a SAT-core re-solve (deferring CDCAC).
        return TheoryCheckResult::mkLemma(newLemmas.front());
    }

    lp << "[LINPROBE] round=" << linRefineRound_
       << " model=" << (modelFilled ? "filled" : "empty")
       << " validated=" << validated << "/" << total
       << " nonlinearNormalized=" << nNonlinearNormalized
       << " newcuts=" << nNewCuts
       << " fp=" << fp.get_str() << " action=CDCAC (cap=" << kRefineCap << ")\n";
    lp.flush();

    // Refinement exhausted (cap hit or dedup-saturated) and no validated model:
    // fall through to the CDCAC backstop (invariant 1: no unvalidated SAT).
    return std::nullopt;
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
