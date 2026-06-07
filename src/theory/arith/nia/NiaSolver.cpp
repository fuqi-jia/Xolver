#include "theory/arith/nia/NiaSolver.h"
#include <algorithm>
#include "theory/arith/dl/DifferenceGraph.h"
#include "theory/arith/dl/BellmanFord.h"
#include "theory/arith/nia/preprocess/VariablePartition.h"
#include "theory/arith/Reasoner.h"
#include <random>
#include "theory/arith/nia/search/NiaLinearizationAdapter.h"
#include "theory/arith/nia/search/NiaIcpAdapter.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/arith/nra/core/CdcacCore.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/arith/nra/engine/ReasonManager.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/nia/farkas/LeafFarkasLia.h"
#include "theory/arith/nra/nla/NlaCutsRunner.h"           // Stage 3 Phase C-3
#include "theory/arith/poly/RationalPolynomial.h"          // Stage 3 Phase C-3
#endif
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/presolve/Presolve.h"
#include "theory/arith/search/CompleteFiniteDomainEnumerator.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "proof/ArithModelValidator.h"
#include "util/EnvParam.h"
#include <functional>
#include <set>
#include "theory/arith/nia/farkas/FarkasOrDetector.h"
#include "theory/arith/nia/farkas/FarkasOrSolver.h"
#include "theory/arith/nia/farkas/FarkasOrModelAssembler.h"
#include "util/MpqUtils.h"
#include <chrono>
#include <iostream>

namespace xolver {
void NiaSolver::setCoreIr(const CoreIr* ir) {
    coreIr_ = ir;
    bbArrayGate_ = -1;  // recompute array-presence for the new IR (bit-blast gate)
    // Track A Phase 1.3: forward CoreIr to the ModEqConstReasoner so its
    // Variable-name extraction has access to expression nodes.
    modEqConst_.setCoreIr(ir);
    // Farkas-Or Phase 0: env-gated structural dump. Bypasses std::cerr
    // (which xolver-cli silently consumes); writes to the file named by
    // XOLVER_NIA_FARKAS_DUMP_FILE if set, else /tmp/farkas_dump.
    if (std::getenv("XOLVER_NIA_FARKAS_DUMP") && ir != nullptr) {
        const char* path = std::getenv("XOLVER_NIA_FARKAS_DUMP_FILE");
        if (!path || !*path) path = "/tmp/farkas_dump";
        FILE* f = std::fopen(path, "a");
        if (f) {
            farkas::FarkasOrDetector det(*ir);
            auto profile = det.detect();
            std::string s = det.dump(profile);
            std::fwrite(s.data(), 1, s.size(), f);
            std::fputc('\n', f);
            std::fclose(f);
        }
    }
}
} // namespace xolver
#include <unordered_set>
#include <cstdlib>
#include <iostream>

namespace xolver {

NiaSolver::~NiaSolver() = default;

void NiaSolver::setRegistry(TheoryAtomRegistry* reg) {
    registry_ = reg;
    if (kernel_) {
        linAdapter_ = std::make_unique<NiaLinearizationAdapter>(*kernel_, reg);
    }
}

NiaSolver::NiaSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)),
      converter_(std::make_unique<PolynomialConverter>(*kernel_)),
      normalizer_(*kernel_),
      validator_(*kernel_),
      univariate_(*kernel_),
      linearDomain_(*kernel_),
      squareBound_(*kernel_),
      sumOfSquaresBound_(*kernel_),
      intervalEvaluator_(*kernel_),
      algebraic_(*kernel_),
      bounded_(*kernel_),
      localSearch_(*kernel_),
      bitBlast_(*kernel_),
      productPositivity_(*kernel_),
      gcdDivisibility_(*kernel_),
      modularResidue_(*kernel_),
      groebner_(*kernel_),
      modEqConst_(*kernel_, /*ir=*/nullptr),
      dio_(*kernel_) {
    // modEqConst_'s CoreIr* is set in setCoreIr(); until then run() returns
    // NoChange (defensive — no fact processing happens before setCoreIr).
    // Phase 2 reasoner pipeline. Order is load-bearing — it reproduces
    // the original linear check() exactly: normalize first, then the
    // presolve fixpoint, then the legacy NIA-Core engines in sequence,
    // then bounded enumeration / local search / branch. `normalized_`
    // and `domains_` are the shared state threaded across stages.
    auto add = [this](const char* nm,
                      std::optional<TheoryCheckResult> (NiaSolver::*m)(TheoryLemmaStorage&, TheoryEffort)) {
        reasoners_.push_back(std::make_unique<CallbackReasoner>(
            nm, [this, m](TheoryLemmaStorage& db, TheoryEffort e) { return (this->*m)(db, e); }));
    };
    auto addFull = [this](const char* nm,
                      std::optional<TheoryCheckResult> (NiaSolver::*m)(TheoryLemmaStorage&, TheoryEffort)) {
        reasoners_.push_back(std::make_unique<CallbackReasoner>(
            nm, [this, m](TheoryLemmaStorage& db, TheoryEffort e) { return (this->*m)(db, e); },
            /*fullEffortOnly=*/true));
    };
    add("nia.pending",        &NiaSolver::stagePending);
    // §2.3 / §5.1 step 1 — pure-linear active fast path. DEFAULT-OFF
    // (XOLVER_NIA_LINEAR_SHORTCUT=1 to enable for experimentation):
    // in QF_NIA the linear atoms are owned by NIA, not LIA — LIA is
    // present only for combination-side bridging. Returning Consistent
    // here from a pure-linear set therefore skips the linear UNSAT
    // proofs NIA's downstream stages (normalize → presolve → bounded)
    // would have caught (e.g. x<3 ∧ x>3, 2x=1, false-Leq polarity).
    // Sound shortcut requires routing the linear subset to LIA first,
    // which is a NiaLinearizationAdapter wiring change deferred to a
    // future wake (see docs/agents/NLSAT-gap-analysis.md Task A).
    add("nia.linear-shortcut", &NiaSolver::stagePureLinearShortcut);
    // Phase D — dispatch-cache lookup at the FRONT of the pipeline. On a
    // signature hit, skip the entire 16-stage pipeline. Default-OFF flag
    // XOLVER_NIA_DISPATCH_CACHE. No-op when the flag is unset.
    add("nia.dispatch-cache", &NiaSolver::stageDispatchCacheLookup);
    add("nia.normalize",      &NiaSolver::stageNormalize);
    // Track A Phase 1.3 — native (mod x y) = c reasoner. Runs early so its
    // bound narrowings feed downstream linear/domain stages. Default-OFF via
    // XOLVER_NIA_NATIVE_MODEQCONST.
    add("nia.mod-eq-const",   &NiaSolver::stageNativeModEqConst);
    // Phase 3b (XOLVER_NIA_BOUNDED_PARTIAL_EARLY, default-OFF). Run the
    // partial bounded enumerator EARLY, right after normalize, before
    // any of the heavy per-propagation stages. On QF_ANIA / QF_AUFNIA /
    // SAT14-class inputs Phase 3a measurement showed the late
    // nia.bounded stage never fires within budget because upstream
    // stages exhaust it; placing solvePartial here gives it first crack
    // on every cb_propagate while the work is still cheap. The lever
    // is SAT-finding only; it returns Sat with a validator-confirmed
    // model or falls through to the rest of the pipeline. Algorithm
    // unchanged from Phase 3a (BoundedNiaSolver::solvePartial) — this
    // flag controls PLACEMENT, not algorithm.
    add("nia.bounded-early",  &NiaSolver::stageBoundedEarly);
    // SAT14-attack: LS pre-pass before any heavy stage. Standard+Full
    // — Full-effort-only registration was tested empirically and loses
    // 100% of the SAT14 wins, because by the time the Full check fires
    // the upstream Full stages (modular, bit-blast, cdcac) have already
    // consumed the budget. Standard-effort firing is what gives LS the
    // CPU it needs to find SAT14 models BEFORE bit-blast starts grinding.
    // The trade-off: on small cases where bit-blast was finding Sat
    // quickly (e.g. 967.smt2, 117.smt2), Standard-effort LS adds enough
    // per-cb_propagate cost to push them past the timeout. Default-OFF
    // for that reason — opt in via XOLVER_NIA_LS_EARLY when explicitly
    // targeting SAT14-class bilinear SAT instances.
    add("nia.local-search-early", &NiaSolver::stageLocalSearchEarly);
    // H3 (master 2026-06-01) SAT14-attack routing. Bit-blast is the right
    // tool for VeryMax-SAT14-class inputs (800+ bounded integer vars,
    // termination certificate solving), but its Full-only registration
    // means the SAT layer's incomplete assignment never triggers it
    // within budget. Standard+Full registration follows the same pattern
    // as nia.local-search-early. Gated default-OFF behind XOLVER_NIA_BB_EARLY.
    add("nia.bit-blast-early", &NiaSolver::stageBitBlastEarly);
    // L4 (XOLVER_NIA_PRESOLVE_FULL, default-OFF). The presolve fixpoint
    // (PresolveEngine + IntLinearEqualityCoreHNF + CompleteFiniteDomainEnumerator)
    // is the per-propagation hot stage on engine-reaching QF_NIA (profiled:
    // ~1.1s/call on dense Dartagnan, and re-run ~8000x at Standard effort on mcm).
    // Gating it to Full-effort only is a perf win, BUT it is NOT verdict-
    // preserving in general: some Standard-effort presolve UNSATs are lost to
    // unknown at Full effort (e.g. the Zohar intand/intor bit-width cases regress
    // unsat -> unknown). So keep it gated default-OFF until that completeness gap
    // is closed; promote only after the unit + regression gate stays green ON.
    //
    // Iter#24 measurement: 16 reg buckets + AProVE 100-sample pass with
    // XOLVER_NIA_PRESOLVE_FULL=1 under iter#21's 50 ms presolve deadline cap.
    // BUT the Zohar intand/intor cases are not in the local reg suite, so this
    // is necessary-but-not-sufficient evidence — promotion requires a panda
    // differential that exercises the historic Zohar regression.
    //
    // Use env::paramInt instead of getenv so the autotuner dump
    // (XOLVER_DUMP_PARAMS) sees this knob in its registered-param list.
    if (env::paramInt("XOLVER_NIA_PRESOLVE_FULL", 0) != 0)
        addFull("nia.presolve", &NiaSolver::stagePresolveFixpoint);
    else
        add("nia.presolve",     &NiaSolver::stagePresolveFixpoint);
    // Stage 3 Phase C-3: NLA-cuts derived from single-var bounds. Gated
    // on XOLVER_NIA_NLA_CUTS (default-OFF), Full-effort only to avoid the
    // per-cb_propagate hot path (the cut-extraction is O(n) over normalized_
    // + an O(n) cut emit; cheap, but Full-only matches the lever's "redundant
    // tightening for hard cases" intent and avoids cost on easy SAT cases).
    addFull("nia.nla-cuts",   &NiaSolver::stageNlaCuts);
    add("nia.trivial-const",  &NiaSolver::stageTrivialConstants);
    add("nia.poly-conflict",  &NiaSolver::stagePolyConflict);
    add("nia.diff-conflict",  &NiaSolver::stageDifferenceConflict);
    add("nia.domain",         &NiaSolver::stageDomainInference);
    add("nia.square-bound",   &NiaSolver::stageSquareBound);
    add("nia.sos-bound",      &NiaSolver::stageSumOfSquares);
    // L2 (default-ON). The univariate rational-root search (findIntegerRoots ->
    // divisors, O(sqrt|a0|) bignum modulos) re-runs on EVERY Standard-effort
    // cb_propagate. On EVM mod-2^256 inputs |a0| ~ 2^256 => an effective
    // per-propagation hang (profiled). Gated to Full-effort only, mirroring
    // nia.local-search / nia.bit-blast: Standard propagation stays cheap; the
    // root search runs at the Full-effort model check and is validated, so
    // completeness/soundness are preserved.
    addFull("nia.univariate", &NiaSolver::stageUnivariate);
    add("nia.algebraic",      &NiaSolver::stageAlgebraic);
    add("nia.product-pos",    &NiaSolver::stageProductPositivity);
    add("nia.gcd",            &NiaSolver::stageGcdDivisibility);
    add("nia.groebner",       &NiaSolver::stageGroebner);
    add("nia.icp",            &NiaSolver::stageIcp);
    add("nia.interval",       &NiaSolver::stageInterval);
    add("nia.linearize",      &NiaSolver::stageLinearization);
    add("nia.bounded",        &NiaSolver::stageBounded);
    // L3 modular residue refutation (default-ON). Sound
    // UNSAT-only (invariant 7). Full-effort only — the bounded residue
    // enumeration must not re-run on every Standard-effort cb_propagate (the
    // per-propagation pathology that motivated the L1/L2 gates). Registered
    // BEFORE nia.bit-blast so it refutes the modular `mod 2^k` structure before
    // the blaster (which times out / OOMs on those inputs) is even attempted.
    addFull("nia.modular",    &NiaSolver::stageModular);
    // Escalating-bounded SAT-finder for unbounded-≥0 vars (XOLVER_NIA_BOUNDED_
    // ESCALATE, default-OFF). Runs BEFORE bit-blast because exact-integer
    // enumeration on a small cap is cheaper than encoding+SAT-solving for the
    // AProVE-class cases where K=2..3 already finds a witness. Sound: every
    // SAT validated by validator_ over the ORIGINAL constraint set.
    addFull("nia.escalating-bounded", &NiaSolver::stageEscalatingBounded);
    // Symbolic modular Diophantine refutation. BEFORE bit-blast so it can
    // refute mod-2^k-structured UNSAT (which the blaster TOs/OOMs on) via exact
    // symbolic congruence reasoning rather than residue enumeration.
    addFull("nia.dio",        &NiaSolver::stageDio);
    addFull("nia.bit-blast",  &NiaSolver::stageBitBlast);
    // Integer-aware CDCAC: the complete UNSAT lever for the hard nonlinear
    // residual. Full-effort only (heavy); runs after the SAT workhorses.
    addFull("nia.cdcac",      &NiaSolver::stageCdcac);
    // Local search is a heuristic SAT-candidate finder; run it ONLY at Full
    // effort (like bit-blast). At Standard effort it re-ran from scratch on
    // every CDCL(T) theory-check (~225x on some QF_NIA), burning ~10s, and is
    // futile on UNSAT. Any model it would find mid-search is still found at the
    // Full-effort check and validated -- so soundness/SAT-finding is preserved.
    addFull("nia.local-search", &NiaSolver::stageLocalSearch);
    // LS-SMART-Z5 (master 2026-06-02): Boolean-extend re-validate.
    // Fires AFTER stageLocalSearch — when LS's strict cost==0 gate failed
    // but LS visited a lowest-cost candidate that may STILL satisfy the
    // full formula via a different Boolean valuation than the SAT layer's
    // current branch. Walks coreIr_ via ArithModelValidator (exact). Sound;
    // never claims UNSAT. Default-OFF XOLVER_NIA_LS_BOOL_EXTEND.
    addFull("nia.local-search-bool-extend", &NiaSolver::stageLocalSearchBoolExtend);
    // HYB-3 (master 2026-06-02 H5 finding) — Standard+Full registration
    // mirrors stageBitBlastEarly / stageLocalSearchEarly. On SAT14-class
    // inputs, Full-effort is unreachable in budget; HYB-3 must fire at
    // Standard effort to have any chance. Gated default-OFF.
    add("nia.hyb-bb-ls", &NiaSolver::stageHybridBbLs);
    // LBBB Phase 2 — fires AFTER local-search has had its chance and
    // marked itself failed. Bit-blast over the box LS explored.
    // Full-effort only; gated default-OFF behind XOLVER_NIA_LBBB.
    addFull("nia.lbbb", &NiaSolver::stageBoundedBitBlast);
    // HYB-2 fires AFTER LBBB so it's the "second-shot" when LBBB also
    // didn't find SAT. Pins U vars at LS-midpoint, leaves B vars free
    // for BB. Full-effort only; gated default-OFF XOLVER_NIA_HYB_LS_BB.
    addFull("nia.hyb-ls-bb", &NiaSolver::stageHybridLsBb);
    // Farkas-Or model constructor (user 2026-06-02). For disjunctive
    // Farkas-certificate-synthesis problems (VeryMax/Stroeder), build
    // a structural CSP over (B, choice, CT), search via GAC backtrack,
    // assemble candidate model, validate against original CoreIr via
    // ArithModelValidator. Returns SAT on validation pass; never UNSAT.
    // Standard+Full so it can fire BEFORE the expensive LS / BB stages
    // that the SAT-layer's theory checks usually exhaust. Default-OFF.
    // Standard+Full. cb_propagate now handles Unknown (mirrors
    // cb_check_found_model), so the streak-3 Unknown bail terminates
    // SAT and lets Cap. 10 promote the validated model.
    add("nia.farkas-or", &NiaSolver::stageFarkasOr);
    add("nia.pending-lemma",  &NiaSolver::stagePendingLemma);
    // Phase D — dispatch-cache record at the TAIL (right before branch).
    // Reaching here means every earlier stage returned nullopt, so the
    // pipeline will fall through to consistent(). Memoize the active_
    // signature so the next identical call hits stageDispatchCacheLookup.
    add("nia.dispatch-cache-record", &NiaSolver::stageDispatchCacheRecord);
    add("nia.branch",         &NiaSolver::stageBranch);
    // Iter#26 RECORD (NOT a flag — the experiment hung the solver, see
    // iter#27 below): gating nia.pending-lemma + nia.branch to Full effort
    // (via a XOLVER_NIA_COMB_DEFER_LEMMA flag) was the iter#25-26 hypothesis
    // for unblocking the QF_ANIA combination starvation diagnosed at
    // TheoryManager.cpp:482 (`return tr` on first non-Consistent). The
    // hypothesis was that deferring NIA's Lemma emission at Standard would
    // let SAT explore + NIA return Consistent + combination layer's
    // getDeducedSharedEqualities + sharedTermArithValue actually fire.
    //
    // Iter#27 measurement on sum10 (QF_ANIA): with the flag on, the solver
    // HANGS — exit=124 (SIGTERM @ 2 s) vs exit=0 (clean "unknown") on
    // default. ZERO stderr output during the 2 s window: no STAGE-PROF,
    // no CONFLICT-SRC, no diag prints. Without nia.branch, SAT continues
    // pure-bool decisions WITHOUT theory feedback and gets stuck in deep
    // exploration of a 3.4 KB formula with ~100 atoms — exponential
    // without theory pruning. Even though the flag was default-OFF, the
    // semantics-when-enabled were actively harmful, so the experiment was
    // reverted entirely (this comment is the documentation; no flag ships).
    //
    // Real iter#27+ paths (unchanged from iter#26):
    //   (a) TheoryManager runs combination AFTER Lemma return (semantic
    //       risk to N-O ordering).
    //   (b) Refactor ~10 NIA Conflict-emit stages to be Full-only AND
    //       redesign the SAT-feedback contract so SAT doesn't starve.
    //   (c) Parallel theory-check / combination architecture (deep).

    // Wiring-level switch (A7): disable the bit-blast stage to expose the pure
    // reasoning path. The backend is uncapped on this base and OOMs on dense
    // AProVE inputs before any reasoning verdict, masking 357-refutation work.
    // Default-on preserved; only an explicit non-empty/non-"0" value turns it off.
    if (const char* e = std::getenv("XOLVER_NIA_NO_BITBLAST"); e && *e && *e != '0')
        enableBitBlast_ = false;

    // Bound-free product-positivity refutation (default-ON). Sound: only
    // derives lower bounds via valid integer implications and reports UNSAT
    // solely from an emptied domain (invariant 7).

    // Multivariate GCD-divisibility refutation (default-ON). Sound: every
    // monomial is an integer, so Σ aᵢmᵢ ≡ 0 (mod gcd aᵢ); g ∤ const ⇒ UNSAT.

    // L3 modular residue refutation (default-ON). Sound: only emits UNSAT,
    // and only when the system has no solution modulo a constant power-of-two
    // modulus (an integer solution would project to one) — invariant 7.

    // Polynomial-ideal saturation (default-OFF). Sound: 1∈ideal ⇒ no ℂ-root ⇒
    // no ℤ-root ⇒ UNSAT (Nullstellensatz direction); bounded Buchberger.
    // iter-77 cherry-pick of 7afeda9 — Step 5 Gröbner-lite (env var renamed
    // ZOLVER_* → XOLVER_* to match this branch's naming convention).
    if (const char* e = std::getenv("XOLVER_NIA_GROBNER"); e && *e && *e != '0')
        enableGroebner_ = true;

    // Interval contraction fixpoint over the existing icp/ engine (default-ON).
    // Sound: only narrows domains via valid bound propagation; UNSAT reported
    // solely from a contractor conflict or an emptied domain (invariant 7).

    // Integer-aware CDCAC (default-OFF). Sound: a CDCAC covering-UNSAT over the
    // real relaxation implies integer-UNSAT (ℤⁿ⊆ℝⁿ; gated by CdcacCore's own
    // unsatTrustworthy_); a CDCAC SAT sample is accepted only when every
    // coordinate is an exact integer AND it passes IntegerModelValidator.
    if (const char* e = std::getenv("XOLVER_NIA_CDCAC"); e && *e && *e != '0')
        enableCdcac_ = true;

    // Incremental normalize cache (default-ON).
    // nia.normalize re-normalized the FULL active_ set on every cb_propagate
    // (Standard effort) — profiled as the per-propagation hot stage on dense
    // QF_UFNIA (NiaNormalizer::normalize -> clearDenominators ->
    // getIntegerCoefficients builds an lp_assignment per constraint per call).
    // normalizeOne is a pure function of its (immutable) ActiveNiaConstraint,
    // and active_ is a strict stack (push_back on assert, resize-from-end on
    // backtrack, clear on reset). So normalized_ is kept in lockstep with
    // active_: onBacktrack truncates it (killing the pop-then-push staleness
    // hazard), onReset clears it, and stageNormalize only normalizes the new
    // tail. Output is byte-identical to the full re-normalize. Default-ON; the
    // cache is bypassed at runtime when ifaceLifecycleEnabled_ (see stageNormalize).

    // XOLVER_NIA_IFACE_LIFECYCLE (default-OFF): decouple Nelson-Oppen interface
    // (dis)equalities from the active_/trail_/activeSet_ back-pop machinery (see
    // member doc). Fixes the false-Unknown that blocked QF_UFNIA/QF_ANIA sats.
    //
    // E1 verification (2026-06-01, agent/eqna-2): A/B on 191 UFNIA cases
    // (100 uniform + 91 Zohar) shows 0 unsound + recovery direction positive
    // (+4 decided locally, expected ~22 at master 5min scale per gdb diagnosis
    // in #26). Track 3 (UF model extraction, #18) is shipped, clearing the
    // earlier "prerequisite" gating. RECOMMEND default-ON: master batch needs
    // XOLVER_NIA_IFACE_LIFECYCLE=1 added to run_differential.sh CANDFLAGS; if
    // 5min batch confirms 0-disagreement, this getenv guard can be removed
    // (mirror the flag-cleanup-final pattern).
    //
    // E2 finding (QG-classification UF/EUF perf gap, 30-case A/B): no single
    // EUF flag gives a useful win on QG-class — EUF_PROP=1 alone yields +1/30,
    // EUF_PROP+BUDGET=2048 *regresses* -1/30 (over-propagation thrashes the
    // SAT layer). The +363 master gap on qg6+qg7 is a SAT/EUF perf wall, not a
    // missing capability — closing it needs decision-heuristic / saturation-
    // efficiency engineering, not a new flag. (See QG bench results in commit.)
    //
    // E3 finding (eq_diamond +81 master gap, 30-case A/B at 5s): EUF_PROP=1
    // gives 0 recovery (A=4 B=4 rec=0 — eq_diamond cases mostly TO at WSL
    // 5s regardless of flag). Master 5min batch sees +81 gap because cases are
    // tractable at 300s — SAME root-cause class as E2 (QG) and Bouvier wipe:
    // SAT/EUF saturation perf wall, not capability. All three clusters need
    // the same engineering work (decision heuristic + e-graph saturation
    // throughput), which is a multi-day surgical project outside this charter.
    //
    // Net E2/E3 outcome: no shippable flag; the perf wall is real and shared
    // across QG / eq_diamond / Bouvier. E1 (lifecycle) remains the one E*
    // win this round.
    //
    // Attack-list overflow probes (cas +25, sqrtmodinv +18): both clusters TO
    // for xolver AND z3 at WSL 8-30s — z3 wins at master 30-300s via mature
    // CAC tuning. These belong to the NRA-agent's CAC perf lane (and the NIA
    // modular reasoner for sqrtmodinv-style families), not EQNA's combination/
    // EUF seam. Routing: defer to NRA agent.
    // Default-ON (header). Env =0 disables (A/B escape).
    if (const char* e = std::getenv("XOLVER_NIA_IFACE_LIFECYCLE")) {
        ifaceLifecycleEnabled_ = !(e[0] == '0' && e[1] == '\0');
    }
}

void NiaSolver::onReset() {
    // Base clears state_.trail + its pending slot; NIA clears its own
    // polynomial stack, active literal set, level-tagged pendings, and
    // combination state.
    bbEarlyUnkSize_ = static_cast<size_t>(-1);  // bit-blast-early dedup cache
    active_.clear();
    trail_.clear();
    normalized_.clear();  // incremental normalize cache is keyed to active_
    activeSet_.reset();
    pendingConflict_.reset();
    pendingUnknown_.reset();
    currentModel_.reset();
    emittedSplits_.clear();
    branchCountPerVar_.clear();
    pendingLinLemmas_.clear();
    interfaceEqualities_.clear();
    interfaceDisequalities_.clear();
    localSearch_.resetBudget();
    localSearch_.resetLsContext();
    // L4.1 modular warm-start: clear memoization for the new solve.
    modularSignatureValid_ = false;
    modularLastSignature_ = 0;
    modularLastWasNoChange_ = false;
    // Phase D: clear dispatch cache for the new solve.
    dispatchCacheValid_ = false;
    dispatchCacheSignature_ = 0;
    // HYB-1: reset partition DIAG once-per-solve guard.
    partitionDiagPrinted_ = false;
}

// L3.1 — per-solve LS pre-pass via check() override, ported from NRA
// agent's fea2d98. Runs ONCE per solve (lsAttempted_ guard) with the
// current active_ set, BEFORE the Reasoner pipeline. If LS finds a
// model that exact-validates, the candidate is cached in
// `lsCachedCandidate_` (persistent across cb_propagate — assertLit does
// NOT clear it) and `currentModel_` is set for the verdict path. On
// every subsequent check() the cached candidate is re-validated against
// the up-to-date active_; if it still satisfies, `currentModel_` is
// re-set and we return consistent. If revalidation fails, the cache is
// dropped and we fall through to the normal pipeline.
//
// CRITICAL DESIGN DECISION (lesson from the previous failed attempt
// that hung pipeline state on every SAT14 case): build a LOCAL
// normalized vector here via `normalizer_.normalizeOne(active_[i])` —
// DO NOT mutate `normalized_`. The pipeline's stageNormalize manages
// `normalized_` with an incremental cache; manually pre-populating it
// races with stageNormalize and corrupts SAT-finding paths. The local
// vector is purely for the LS pre-pass + validation; it is discarded
// at function exit. stageNormalize then sees `normalized_` exactly as
// it would in the OFF path.
//
// Sound under invariant 1: every consistent() emit is backed by
// IntegerModelValidator on the candidate against the LOCAL normalized
// constraints (which are equivalent to active_ up to the pure
// normalizeOne transform); never reports SAT with an unconfirmed model.
void NiaSolver::assertLit(const TheoryAtomRecord& atom, bool value,
                          int level, SatLit assertedLit) {
    auto r = activeSet_.insert(assertedLit);
    if (r == ActiveLiteralSet::InsertResult::Duplicate) {
        return;
    }
    if (r == ActiveLiteralSet::InsertResult::OppositePolarity) {
        static const bool oppDiag = std::getenv("NIA_OPP_DIAG") != nullptr;
        if (oppDiag) {
            std::cerr << "[NIA-OPP] satVar=" << assertedLit.var
                      << " sign=" << (int)assertedLit.sign
                      << " level=" << level
                      << " currentLevel=" << state_.currentLevel
                      << " active=" << active_.size()
                      << " trail=" << state_.trail.size() << "\n";
        }
        pendingUnknown_ = PendingUnknown{level};
        return;
    }

    state_.trail.push_back({level, assertedLit, atom, value});
    if (level > state_.currentLevel) state_.currentLevel = level;

    const auto* payload = std::get_if<PolynomialAtomPayload>(&atom.payload);
    if (!payload) {
        pendingUnknown_ = PendingUnknown{level};
        return;
    }

    // An algebraic RHS cannot be represented in the rational polynomial kernel
    // (it would need an algebraic constant term).  This never arises from
    // rational SMT inputs; if it ever does, fall back to Unknown rather than
    // silently dropping the bound.
    auto rhsQ = payload->rhs.tryAsRational();
    if (!rhsQ) {
        pendingUnknown_ = PendingUnknown{level};
        return;
    }

    size_t oldSize = active_.size();
    Relation rel = value ? payload->rel : negateRelation(payload->rel);
    // Phase D: a fresh asserted literal changes active_ semantics — any
    // cached "consistent at signature X" is now stale.
    dispatchCacheValid_ = false;

    // Normalize (poly - rhs) rel 0 form
    PolyId diff = payload->poly;
    if (*rhsQ != 0) {
        PolyId rhsPoly = kernel_->mkConst(*rhsQ);
        diff = kernel_->sub(payload->poly, rhsPoly);
    }

    active_.push_back({diff, rel, assertedLit});
    trail_.push_back({level, oldSize});
}

void NiaSolver::onBacktrack(int level) {
    // Base already removed state_.trail entries with level > target.
    // Roll back the polynomial constraint stack in lockstep. With the lifecycle
    // fix on, interface (dis)equalities are NOT on active_/trail_, so this loop
    // touches only the (monotonic-by-level) normal-atom stack.
    while (!trail_.empty() && trail_.back().level > level) {
        active_.resize(trail_.back().activeSizeBefore);
        trail_.pop_back();
    }
    // Keep the incremental normalize cache in lockstep: drop the popped tail so
    // a subsequent pop-then-push (same net size, different tail) can't read a
    // stale normalized_ entry. The next stageNormalize re-normalizes only the
    // fresh tail. No-op when normCache_ is off (normalized_ is rebuilt anyway).
    if (normalized_.size() > active_.size())
        normalized_.resize(active_.size());
    activeSet_.rebuildFromActive(active_, [](const auto& c) { return c.reason; });
    // L4.1: backtrack invalidates modular memoization. The constraint
    // set just shrank; the cached NoChange verdict was for a strictly
    // larger set and may not transfer (a smaller set could still be
    // NoChange, but signature mismatch makes us re-run conservatively).
    modularSignatureValid_ = false;
    // Phase D: backtrack invalidates the dispatch cache. The state
    // signature recorded by the cache is no longer current.
    dispatchCacheValid_ = false;
    if (pendingConflict_ && pendingConflict_->level > level) {
        pendingConflict_.reset();
    }
    if (pendingUnknown_ && pendingUnknown_->level > level) {
        pendingUnknown_.reset();
    }
    // A full reset (backtrack to level 0) clears ALL interface (dis)equalities so
    // they are re-driven fresh by the next check(). This prevents level-0
    // interface eqs — assigned at the SAT root, or given level 0 by the
    // Full-effort model-check re-drive's levelOf() fallback — from accumulating
    // across the many model checks (the back-pop never removes level-0 entries).
    // Otherwise drop only those strictly above the backtrack target.
    bool fullReset = ifaceLifecycleEnabled_ && level == 0;
    auto ieIt = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
        [&](const auto& ie) { return fullReset || ie.level > level; });
    interfaceEqualities_.erase(ieIt, interfaceEqualities_.end());
    auto idIt = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
        [&](const auto& ie) { return fullReset || ie.level > level; });
    interfaceDisequalities_.erase(idIt, interfaceDisequalities_.end());
}

static std::unordered_set<std::string> collectVars(
    const std::vector<NormalizedNiaConstraint>& constraints,
    PolynomialKernel& kernel) {
    std::unordered_set<std::string> vars;
    for (const auto& c : constraints) {
        for (const auto& v : kernel.variables(c.poly)) {
            vars.insert(v);
        }
    }
    return vars;
}

// ---------------------------------------------------------------------------
// Reasoner pipeline stages (Phase 2). Verbatim decomposition of the former
// linear check() body. Each stage returns nullopt to fall through to the
// next, or a TheoryCheckResult to stop. `normalized_` and `domains_` are the
// shared state threaded across stages.
// ---------------------------------------------------------------------------

std::optional<TheoryCheckResult> NiaSolver::stagePending(TheoryLemmaStorage&, TheoryEffort) {
    if (pendingUnknown_) return TheoryCheckResult::unknown("NIA: pending unknown (opposite polarity asserted)");
    if (pendingConflict_) return TheoryCheckResult::mkConflict(pendingConflict_->conflict);
    // With the lifecycle fix on, interface (dis)equalities live off active_, so
    // an empty active_ may still carry combination obligations to solve.
    if (active_.empty() &&
        (!ifaceLifecycleEnabled_ ||
         (interfaceEqualities_.empty() && interfaceDisequalities_.empty())))
        return TheoryCheckResult::consistent();
    return std::nullopt;
}

// §2.3 / §5.1 step 1 — pure-linear active-set shortcut.
//
// Reads each active ActiveNiaConstraint's polynomial; if every constraint
// is linear (no monomial has total degree > 1), NIA has no nonlinear
// obligation. LIA is registered alongside NIA by TheoryFactory and owns
// the linear check in the same CDCL(T) round, so NIA can return
// Consistent immediately and skip the 16 downstream nonlinear stages.
//
// Sound: NIA's job is nonlinear reasoning; with no nonlinear atom the
// verdict on `active_` is definitionally LIA's verdict. Returning
// Consistent here adds no claim — it just defers to the linear sibling.
//
// Soundness floor: if any term cannot be decomposed (`terms()` returns
// nullopt — e.g. non-integer coefficients), we conservatively fall
// through so a downstream stage handles it.
std::optional<TheoryCheckResult> NiaSolver::stagePureLinearShortcut(
    TheoryLemmaStorage&, TheoryEffort) {
    // DEFAULT-OFF — see registration comment for the soundness reason.
    const char* e = std::getenv("XOLVER_NIA_LINEAR_SHORTCUT");
    if (!e || !*e || e[0] == '0') return std::nullopt;
    if (active_.empty()) return std::nullopt;  // stagePending handles empty
    for (const auto& a : active_) {
        auto terms = kernel_->terms(a.poly);
        if (!terms) return std::nullopt;  // can't decompose → defer
        for (const auto& term : *terms) {
            int total = 0;
            for (const auto& [vid, exp] : term.powers) {
                (void)vid;
                total += exp;
                if (total > 1) return std::nullopt;  // nonlinear → defer
            }
        }
    }
    // All active atoms are linear; LIA owns this.
    return TheoryCheckResult::consistent();
}

// Phase D — FNV-1a hash of the active_ signature: count + sequence of
// (satVar, sign) drawn from state_.trail + interface-eq/diseq counts.
// Cheap, deterministic, collision-resistant enough for the cache use
// case (a stale hit would only re-run the pipeline next call, never a
// soundness concern — the cache only short-circuits identical inputs).
namespace {
uint64_t fnv1aMix(uint64_t h, uint64_t x) {
    h ^= x;
    h *= 1099511628211ull;
    return h;
}
uint64_t computeDispatchSignature(
    size_t activeSize,
    const std::vector<std::pair<uint32_t, bool>>& satTrail,
    size_t ieCount, size_t idCount) {
    uint64_t h = 14695981039346656037ull;  // FNV offset basis
    h = fnv1aMix(h, activeSize);
    h = fnv1aMix(h, satTrail.size());
    for (const auto& p : satTrail) {
        h = fnv1aMix(h, static_cast<uint64_t>(p.first));
        h = fnv1aMix(h, p.second ? 1ull : 0ull);
    }
    h = fnv1aMix(h, ieCount);
    h = fnv1aMix(h, idCount);
    return h;
}
}  // namespace

std::optional<TheoryCheckResult> NiaSolver::stageDispatchCacheLookup(TheoryLemmaStorage&, TheoryEffort) {
    static const bool dcEnabled = [] {
        const char* e = std::getenv("XOLVER_NIA_DISPATCH_CACHE");
        return e && *e && *e != '0';
    }();
    if (!dcEnabled) return std::nullopt;
    if (!dispatchCacheValid_) return std::nullopt;
    // Collect (satVar, sign) pairs from state_.trail (the canonical
    // record of asserted literals, kept in lockstep with active_).
    std::vector<std::pair<uint32_t, bool>> satTrail;
    satTrail.reserve(state_.trail.size());
    for (const auto& a : state_.trail) {
        satTrail.emplace_back(a.lit.var, a.lit.sign);
    }
    const uint64_t sig = computeDispatchSignature(
        active_.size(), satTrail,
        interfaceEqualities_.size(), interfaceDisequalities_.size());
    if (sig == dispatchCacheSignature_) {
        // Identical state to the last successful consistent run.
        // Verdict-preserving short-circuit; sound because the cached
        // consistent verdict was produced by the full pipeline at this
        // signature in the same scope (any backtrack / reset / assertLit
        // would have invalidated dispatchCacheValid_ already).
        return TheoryCheckResult::consistent();
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageDispatchCacheRecord(TheoryLemmaStorage&, TheoryEffort) {
    static const bool dcEnabled = [] {
        const char* e = std::getenv("XOLVER_NIA_DISPATCH_CACHE");
        return e && *e && *e != '0';
    }();
    if (!dcEnabled) return std::nullopt;
    // Reaching this stage means every earlier stage returned nullopt
    // (the base pipeline will fall through to consistent()). Record
    // the signature so the next identical call hits the lookup
    // short-circuit.
    std::vector<std::pair<uint32_t, bool>> satTrail;
    satTrail.reserve(state_.trail.size());
    for (const auto& a : state_.trail) {
        satTrail.emplace_back(a.lit.var, a.lit.sign);
    }
    dispatchCacheSignature_ = computeDispatchSignature(
        active_.size(), satTrail,
        interfaceEqualities_.size(), interfaceDisequalities_.size());
    dispatchCacheValid_ = true;
    return std::nullopt;  // fall through to consistent()
}

std::optional<TheoryCheckResult> NiaSolver::stageNormalize(TheoryLemmaStorage&, TheoryEffort) {
    // HYB-1 DIAG hook (XOLVER_NIA_VAR_PARTITION_DIAG=1) — once per solve.
    // Placed at the TOP of stageNormalize so both the normCache fast-path
    // and the full-normalize path are exercised. Fires after normalized_
    // has been populated (i.e., after the cache update below). Cheap.
    auto emitPartitionDiag = [this]() {
        static const bool partDiag = std::getenv("XOLVER_NIA_VAR_PARTITION_DIAG") != nullptr;
        if (partDiag && !partitionDiagPrinted_ && !normalized_.empty()) {
            partitionDiagPrinted_ = true;
            VariablePartition vp(*kernel_);
            auto pr = vp.partition(normalized_, domains_, 32);
            std::fprintf(stderr,
                "[HYB-1] vars=%zu |B|=%zu (avgBW=%.1f maxBW=%u) |U|=%zu  asserts=%zu\n",
                pr.totalVars(), pr.boundedCount(),
                pr.averageBitWidthBounded(), pr.maxBitWidthBounded(),
                pr.unboundedCount(), normalized_.size());
            std::fflush(stderr);
        }
    };
    // Incremental normalize cache (default-ON): normalized_ is kept in
    // lockstep with the strict active_ stack — normalize only the new tail
    // (normalizeOne is pure per-constraint, so this is byte-identical to a full
    // re-normalize). Safety-truncate in case a backtrack left it longer.
    // VALID ONLY when the interface-eq lifecycle is NOT merging (dis)eqs into the
    // set: those live off active_ and are re-driven per decision level, which
    // breaks the stack invariant the cache relies on. So under IFACE_LIFECYCLE we
    // fall back to a full re-normalize of the merged set every call.
    if (normCache_ && !ifaceLifecycleEnabled_) {
        if (normalized_.size() > active_.size())
            normalized_.resize(active_.size());
        for (size_t i = normalized_.size(); i < active_.size(); ++i)
            normalized_.push_back(normalizer_.normalizeOne(active_[i]));
        emitPartitionDiag();
        return std::nullopt;
    }
    // Full normalize. With the lifecycle fix on, merge the live interface
    // (dis)equalities into the constraint set here (kept off active_/trail_/
    // activeSet_ to avoid corrupting the back-pop stack — see ifaceLifecycleEnabled_).
    // Each carries its converted (a-b) poly + relation and reason literal, so
    // conflicts cite it correctly. The merge is read-only over active_.
    const std::vector<ActiveNiaConstraint>* toNormalize = &active_;
    std::vector<ActiveNiaConstraint> merged;
    if (ifaceLifecycleEnabled_ &&
        !(interfaceEqualities_.empty() && interfaceDisequalities_.empty())) {
        merged.reserve(active_.size() + interfaceEqualities_.size() +
                       interfaceDisequalities_.size());
        merged = active_;
        for (const auto& ie : interfaceEqualities_)
            if (ie.diff != NullPoly) merged.push_back({ie.diff, ie.rel, ie.reason});
        for (const auto& id : interfaceDisequalities_)
            if (id.diff != NullPoly) merged.push_back({id.diff, id.rel, id.reason});
        toNormalize = &merged;
    }
    auto normalizedOpt = normalizer_.normalize(*toNormalize);
    if (!normalizedOpt) return TheoryCheckResult::unknown("NIA: normalizer failed (non-integer coefficients)");
    normalized_ = std::move(*normalizedOpt);
    // HYB-1 DIAG hook (XOLVER_NIA_VAR_PARTITION_DIAG=1) — once per solve.
    // Fires here so downstream observers see the partition over the
    // normalized constraint set. domains_ may be partially populated;
    // VariablePartition compensates by directly scanning the constraint
    // set for single-var bound atoms in addition to consulting DomainStore.
    emitPartitionDiag();
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stagePresolveFixpoint(TheoryLemmaStorage&, TheoryEffort) {
    // Theory-check presolve fixpoint (Capabilities 1–7, 11). Sound,
    // equivalence-preserving derivations over the active atoms. May return a
    // Conflict (UNSAT) or a case-split Lemma; never SAT directly. Otherwise
    // falls through, having populated derived bounds/substitutions consumed
    // below, then Cap. 9 attempts complete finite-domain enumeration.
    //
    // Iter#21: pass a per-call deadline into PresolveEngine.run() to free
    // SAT-finder stages on QF_ANIA Ozdemir-class. Default 50 ms per call
    // (XOLVER_NIA_PRESOLVE_BUDGET_MS); 0 disables the cap. STAGE-PROF
    // measurement: pre-iter#21 presolve consumed 4769 ms of a 5 s budget
    // (24 cb_propagate × ~200 ms each), starving demand-arrangement /
    // escalating-bounded / LS / AMV from running. SOUND: capping inside
    // the fixpoint exits with the partial fact set already in st_.ledger —
    // every recorded derivation is still semantically valid; downstream
    // stages see a SUBSET of what unbounded presolve would derive, never
    // an incorrect claim.
    static const long presolveBudgetMs =
        env::paramLong("XOLVER_NIA_PRESOLVE_BUDGET_MS", 50);
    PresolveEngine presolve(kernel_.get(), /*integerDomain=*/true);
    bool feasible = true;
    for (const auto& c : normalized_) {
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
        if (pr.kind == PresolveResult::Kind::Conflict) {
            return TheoryCheckResult::mkConflict(pr.conflict);
        }
        if (pr.kind == PresolveResult::Kind::Lemma) {
            return TheoryCheckResult::mkLemma(pr.lemma);
        }
        auto fd = CompleteFiniteDomainEnumerator::run(
            presolve.state(), normalized_, validator_, *kernel_);
        if (fd.status == FiniteDomainResult::Status::Sat) {
            currentModel_ = fd.model;
            return TheoryCheckResult::consistent();
        }
        if (fd.status == FiniteDomainResult::Status::UnsatComplete) {
            return TheoryCheckResult::mkConflict(fd.conflict);
        }
    }
    return std::nullopt;
}

// Stage 3 Phase C-3 — NLA-cuts hook for NiaSolver. Mirrors the NraSolver
// hook (3eb2116) but operates on normalized_ (NormalizedNiaConstraint)
// and appends back into normalized_ so downstream stages see the cuts.
//
// Soundness:
//   Each cut is a logical implication of its source bounds — adding it to
//   normalized_ is sat/unsat preserving. The reason set must be a SINGLE
//   SatLit so it fits the NormalizedNiaConstraint shape (one reason per
//   constraint, matching the cacCons/activeReasons contract on the NRA
//   side); multi-reason cuts (monotonicityProduct, McCormick) are dropped
//   silently — they'd need a synthetic conjunction lit, pinned for the
//   next Phase D commit.
//
// The bound extraction handles c1*v + c0 rel 0 only (single var, degree 1,
// integer-constant c0/c1). Multi-var or nonlinear constraints are skipped.
std::optional<TheoryCheckResult> NiaSolver::stageNlaCuts(TheoryLemmaStorage&,
                                                          TheoryEffort) {
    static const bool nlaCutsEnabled = [] {
        const char* e = std::getenv("XOLVER_NIA_NLA_CUTS");
        return e && *e && *e != '0';
    }();
    if (!nlaCutsEnabled) return std::nullopt;
    if (normalized_.empty()) return std::nullopt;

    std::map<VarId, nla::VarInterval> intervalMap;
    for (const auto& c : normalized_) {
        if (c.poly == NullPoly) continue;
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) continue;
        auto vars = rp->variables();
        if (vars.size() != 1) continue;
        VarId v = *vars.begin();
        if (rp->degree(v) != 1) continue;
        auto coeffs = rp->coefficients(v);
        if (coeffs.size() != 2) continue;
        if (!coeffs[0].isConstant() || !coeffs[1].isConstant()) continue;
        mpq_class c0 = coeffs[0].constantValue();
        mpq_class c1 = coeffs[1].constantValue();
        if (c1 == 0) continue;
        mpq_class bound = -c0 / c1;
        Relation effRel = c.rel;
        if (c1 < 0) {
            switch (effRel) {
                case Relation::Leq: effRel = Relation::Geq; break;
                case Relation::Geq: effRel = Relation::Leq; break;
                case Relation::Lt:  effRel = Relation::Gt;  break;
                case Relation::Gt:  effRel = Relation::Lt;  break;
                case Relation::Eq:  case Relation::Neq: break;
            }
        }
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
        tighter(vi.lo, vi.hi, bound, effRel);
        vi.reasons = {c.reason};
    }
    if (intervalMap.empty()) return std::nullopt;

    std::vector<nla::VarInterval> intervals;
    intervals.reserve(intervalMap.size());
    for (auto& [v, vi] : intervalMap) intervals.push_back(std::move(vi));

    nla::NlaCutsRunner runner(*kernel_);
    auto cuts = runner.runShapeCuts(intervals, /*maxPairs=*/0);
    for (const auto& cut : cuts) {
        if (cut.poly == NullPoly) continue;
        if (cut.reasons.size() != 1) continue;  // single-reason only
        // Append directly into normalized_. Subsequent stages see this as
        // any other NIA constraint; their cb_propagate path handles it.
        NormalizedNiaConstraint nc;
        nc.poly = cut.poly;
        nc.rel = cut.rel;
        nc.reason = cut.reasons[0];
        normalized_.push_back(nc);
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageTrivialConstants(TheoryLemmaStorage&, TheoryEffort) {
    std::vector<SatLit> conflictLits;
    bool hasNonConstant = false;
    for (const auto& c : normalized_) {
        if (!kernel_->isConstant(c.poly)) {
            hasNonConstant = true;
            continue;
        }
        mpq_class val = kernel_->toConstant(c.poly);
        if (!relationSatisfied(val, c.rel)) {
            conflictLits.push_back(c.reason);
        }
    }
    if (!conflictLits.empty()) {
        return TheoryCheckResult::mkConflict(TheoryConflict{conflictLits});
    }
    if (!hasNonConstant) {
        return TheoryCheckResult::consistent();
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stagePolyConflict(TheoryLemmaStorage&, TheoryEffort) {
    // Group active constraints by polynomial. Each is `P rel 0`, i.e. a sign
    // constraint on the value of P. Within one poly the constraints define an
    // interval-around-0 for P's value; if 0 is excluded AND P is pinned to 0 the
    // group is infeasible — a sound conflict (a single-poly Farkas certificate)
    // that needs no domain bounds. This is exactly the QF_UFNIA comparison
    // tautology: `-a+b` asserted both `<0` (a>b) and `>0` (a<b).
    struct Acc {
        bool hasUpper = false, upperStrict = false; SatLit upperReason{};
        bool hasLower = false, lowerStrict = false; SatLit lowerReason{};
        bool hasNeq = false; SatLit neqReason{};
    };
    // `P rel 0` ⟺ `-P flip(rel) 0`, so canonicalize each poly's sign (a form and
    // its negation share one group) — needed because `(= a b)` yields `a-b` while
    // `(>= a b)` yields `-a+b`. Sign-flip of the relation: Lt↔Gt, Leq↔Geq, Eq, Neq.
    auto flipRel = [](Relation r) -> Relation {
        switch (r) {
            case Relation::Lt:  return Relation::Gt;
            case Relation::Gt:  return Relation::Lt;
            case Relation::Leq: return Relation::Geq;
            case Relation::Geq: return Relation::Leq;
            default:            return r;  // Eq, Neq unchanged
        }
    };
    std::unordered_map<std::string, Acc> groups;
    for (const auto& c : active_) {
        auto it = polyCanonCache_.find(c.poly);
        if (it == polyCanonCache_.end()) {
            std::string sP = kernel_->toString(c.poly);
            std::string sN = kernel_->toString(kernel_->neg(c.poly));
            bool flip = sN < sP;
            it = polyCanonCache_.emplace(c.poly,
                     std::make_pair(flip ? sN : sP, flip)).first;
        }
        const std::string& key = it->second.first;
        Relation rel = it->second.second ? flipRel(c.rel) : c.rel;
        Acc& g = groups[key];
        switch (rel) {
            case Relation::Lt:  g.hasUpper = true; g.upperStrict = true; g.upperReason = c.reason; break;
            case Relation::Leq: if (!g.hasUpper) { g.hasUpper = true; g.upperReason = c.reason; } break;
            case Relation::Gt:  g.hasLower = true; g.lowerStrict = true; g.lowerReason = c.reason; break;
            case Relation::Geq: if (!g.hasLower) { g.hasLower = true; g.lowerReason = c.reason; } break;
            case Relation::Eq:
                if (!g.hasUpper) { g.hasUpper = true; g.upperReason = c.reason; }
                if (!g.hasLower) { g.hasLower = true; g.lowerReason = c.reason; }
                break;
            case Relation::Neq: g.hasNeq = true; g.neqReason = c.reason; break;
        }
    }
    // Fold in Nelson-Oppen interface disequalities (a != b shared by EUF). Their
    // diff poly a-b, canonicalized, joins the same group: if the comparison
    // bounds pin a-b to 0 (a=b) while EUF asserts a!=b, that is a sound conflict
    // the NIA-only sign reasoning would otherwise miss (the equality lives in
    // EUF, not NIA). Empty unless XOLVER_NIA_IFACE_LIFECYCLE populates them.
    for (const auto& ie : interfaceDisequalities_) {
        if (ie.diff == NullPoly) continue;
        auto it = polyCanonCache_.find(ie.diff);
        if (it == polyCanonCache_.end()) {
            std::string sP = kernel_->toString(ie.diff);
            std::string sN = kernel_->toString(kernel_->neg(ie.diff));
            bool flip = sN < sP;
            it = polyCanonCache_.emplace(ie.diff,
                     std::make_pair(flip ? sN : sP, flip)).first;
        }
        Acc& g = groups[it->second.first];
        g.hasNeq = true; g.neqReason = ie.reason;  // Neq is sign-invariant
    }
    for (auto& [poly, g] : groups) {
        // P bounded at 0 from both sides; a strict bound on either side makes the
        // only candidate (P=0) infeasible. Reasons: the two crossing constraints.
        if (g.hasUpper && g.hasLower && (g.upperStrict || g.lowerStrict)) {
            return TheoryCheckResult::mkConflict(
                TheoryConflict{{g.upperReason, g.lowerReason}});
        }
        // P pinned to 0 (P<=0 and P>=0) but asserted P!=0.
        if (g.hasUpper && g.hasLower && !g.upperStrict && !g.lowerStrict && g.hasNeq) {
            return TheoryCheckResult::mkConflict(
                TheoryConflict{{g.upperReason, g.lowerReason, g.neqReason}});
        }
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageDifferenceConflict(TheoryLemmaStorage&, TheoryEffort) {
    // Extract difference bounds `i - j <= c` from active `P rel 0` where
    // P == 1*i - 1*j + k, build a DifferenceGraph, and reuse the project's
    // BellmanFord engine to detect a negative cycle (a sound Farkas conflict).
    auto extractDiff = [&](PolyId P, std::string& vi, std::string& vj, mpz_class& k) -> bool {
        auto t = kernel_->terms(P);
        if (!t) return false;
        int nplus = 0, nminus = 0; k = 0;
        for (const auto& m : *t) {
            if (m.powers.empty()) { k += m.coefficient; continue; }
            if (m.powers.size() != 1 || m.powers[0].second != 1) return false;
            std::string v(kernel_->varName(m.powers[0].first));
            if (m.coefficient == 1)       { if (nplus++)  return false; vi = v; }
            else if (m.coefficient == -1) { if (nminus++) return false; vj = v; }
            else return false;
        }
        return nplus == 1 && nminus == 1;
    };
    DifferenceGraph<mpz_class> graph;
    // edge for `x - y <= c`: BellmanFord relaxes dist[to] <= dist[from] + w,
    // i.e. to - from <= w, so from=y, to=x, w=c.
    auto addBound = [&](const std::string& x, const std::string& y,
                        const mpz_class& c, SatLit r) {
        graph.addEdge(graph.getOrCreateNode(y), graph.getOrCreateNode(x), c, r);
    };
    bool any = false;
    for (const auto& con : active_) {
        std::string vi, vj; mpz_class k;
        if (!extractDiff(con.poly, vi, vj, k) || vi == vj) continue;
        // poly = vi - vj + k ; `poly rel 0`  ==>  vi - vj rel -k
        switch (con.rel) {
            case Relation::Leq: addBound(vi, vj, -k, con.reason); any = true; break;
            case Relation::Lt:  addBound(vi, vj, -k - 1, con.reason); any = true; break;
            case Relation::Geq: addBound(vj, vi, k, con.reason); any = true; break;
            case Relation::Gt:  addBound(vj, vi, k - 1, con.reason); any = true; break;
            case Relation::Eq:
                addBound(vi, vj, -k, con.reason);
                addBound(vj, vi, k, con.reason);
                any = true; break;
            case Relation::Neq: break;
        }
        if (graph.numNodes() > 96) return std::nullopt;  // keep BF cheap on big problems
    }
    // Fold Nelson-Oppen interface equalities (a == b, shared by EUF — e.g. the
    // intmodtotal ite's `itevar = r`) as bidirectional difference edges so the
    // difference chain can cross the theory boundary. (Interface diseqs are not
    // difference BOUNDS; stagePolyConflict already handles them.)
    for (const auto& ie : interfaceEqualities_) {
        if (ie.diff == NullPoly) continue;
        std::string vi, vj; mpz_class k;
        if (!extractDiff(ie.diff, vi, vj, k) || vi == vj) continue;
        addBound(vi, vj, -k, ie.reason);   // vi - vj <= -k
        addBound(vj, vi, k, ie.reason);     // vi - vj >= -k
        any = true;
        if (graph.numNodes() > 96) return std::nullopt;
    }
    if (!any) return std::nullopt;
    BellmanFord<mpz_class> bf;
    auto res = bf.runFull(graph);
    if (!res.negativeCycle) return std::nullopt;
    std::vector<SatLit> reasons;
    for (EdgeId eid : res.cycle) {
        SatLit r = graph.edge(eid).reason;
        if (std::none_of(reasons.begin(), reasons.end(),
                         [&](SatLit x){ return x.var == r.var && x.sign == r.sign; }))
            reasons.push_back(r);
    }
    if (reasons.empty()) return std::nullopt;
    return TheoryCheckResult::mkConflict(TheoryConflict{reasons});
}

std::optional<TheoryCheckResult> NiaSolver::stageDomainInference(TheoryLemmaStorage&, TheoryEffort) {
    // 3. Reset domains
    domains_.reset();

    static const bool domDiag = std::getenv("NIA_DOM_DIAG") != nullptr;
    if (domDiag) {
        std::cerr << "[NIA-DOM] normalized constraints (" << normalized_.size() << "):\n";
        for (const auto& c : normalized_) {
            std::cerr << "  reason=" << c.reason.var << " rel=" << (int)c.rel
                      << " poly=" << kernel_->toString(c.poly) << "\n";
        }
    }

    // 4. Linear domain inference
    auto lr = linearDomain_.run(normalized_, domains_);
    if (lr.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*lr.conflict);
    }
    if (lr.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown("NIA: linear domain reasoning fatal unknown");
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }

    // 4.5 Product bound propagation: from a*b = c and a,b > 0 derive upper bounds
    for (const auto& c : normalized_) {
        if (c.rel != Relation::Eq) continue;
        auto termsOpt = kernel_->terms(c.poly);
        if (!termsOpt) {
            continue;
        }
        const auto& terms = *termsOpt;
        const PolynomialKernel::MonomialTerm* quadTerm = nullptr;
        const PolynomialKernel::MonomialTerm* constTerm = nullptr;
        for (const auto& t : terms) {
            if (t.powers.empty()) {
                constTerm = &t;
            } else if (t.powers.size() == 2 && t.powers[0].second == 1 && t.powers[1].second == 1) {
                quadTerm = &t;
            }
        }
        if (!quadTerm || !constTerm) {
            continue;
        }
        // Soundness: the product value x*y = -c0/cq is entailed only when the
        // equality is EXACTLY  cq*x*y + c0 = 0.  If any other term is present
        // (e.g. a*z in  x*y + a*z - 6 = 0), x*y is under-determined and a tight
        // upper bound from -c0/cq wrongly excludes valid solutions (false UNSAT).
        if (terms.size() != 2) {
            continue;
        }
        mpz_class numer = -constTerm->coefficient;
        mpz_class denom = quadTerm->coefficient;
        if (denom == 0) continue;
        if (numer % denom != 0) continue;
        mpz_class product = numer / denom;
        if (product <= 0) continue;

        std::string v1 = std::string(kernel_->varName(quadTerm->powers[0].first));
        std::string v2 = std::string(kernel_->varName(quadTerm->powers[1].first));
        const IntDomain* d1 = domains_.getDomain(v1);
        const IntDomain* d2 = domains_.getDomain(v2);
        if (!d1 || !d2) continue;
        if (!d1->hasLower || d1->lower.value <= 0) continue;
        if (!d2->hasLower || d2->lower.value <= 0) continue;

        mpz_class ub1 = product / d2->lower.value;
        mpz_class ub2 = product / d1->lower.value;
        domains_.addUpperBound(v1, ub1, c.reason);
        domains_.addUpperBound(v2, ub2, c.reason);
    }

    // 4.6 Propagate bounds through equalities (after product bounds)
    for (const auto& c : normalized_) {
        if (c.rel != Relation::Eq) continue;
        auto termsOpt = kernel_->terms(c.poly);
        if (!termsOpt) continue;
        const auto& terms = *termsOpt;
        const PolynomialKernel::MonomialTerm* constTerm = nullptr;
        std::vector<const PolynomialKernel::MonomialTerm*> varTerms;
        for (const auto& t : terms) {
            if (t.powers.empty()) {
                constTerm = &t;
            } else if (t.powers.size() == 1 && t.powers[0].second == 1) {
                varTerms.push_back(&t);
            } else {
                varTerms.clear();
                break;
            }
        }
        if (varTerms.size() != 2) continue;
        if (constTerm && constTerm->coefficient != 0) continue;
        const auto& t1 = *varTerms[0];
        const auto& t2 = *varTerms[1];
        if (t1.coefficient != -t2.coefficient) continue;

        std::string v1 = std::string(kernel_->varName(t1.powers[0].first));
        std::string v2 = std::string(kernel_->varName(t2.powers[0].first));
        const IntDomain* d1 = domains_.getDomain(v1);
        const IntDomain* d2 = domains_.getDomain(v2);
        if (!d1 && !d2) continue;

        // A bound propagated through the equality v1=v2 is justified by BOTH
        // the equality (c.reason) AND the source bound's own reasons. Dropping
        // the latter yields an over-strong (unsound) empty-domain conflict.
        auto withEq = [&](const std::vector<SatLit>& srcReasons) {
            std::vector<SatLit> rs = srcReasons;
            rs.push_back(c.reason);
            return rs;
        };
        auto propagate = [&](const std::string& src, const std::string& dst, const IntDomain* srcDom) {
            (void)src;
            if (!srcDom) return;
            if (srcDom->hasLower) domains_.addLowerBound(dst, srcDom->lower.value, withEq(srcDom->lower.reasons));
            if (srcDom->hasUpper) domains_.addUpperBound(dst, srcDom->upper.value, withEq(srcDom->upper.reasons));
        };

        if (d1 && !d2) propagate(v1, v2, d1);
        else if (!d1 && d2) propagate(v2, v1, d2);
        else if (d1 && d2) {
            if (d1->hasLower && (!d2->hasLower || d1->lower.value > d2->lower.value))
                domains_.addLowerBound(v2, d1->lower.value, withEq(d1->lower.reasons));
            if (d1->hasUpper && (!d2->hasUpper || d1->upper.value < d2->upper.value))
                domains_.addUpperBound(v2, d1->upper.value, withEq(d1->upper.reasons));
            if (d2->hasLower && (!d1->hasLower || d2->lower.value > d1->lower.value))
                domains_.addLowerBound(v1, d2->lower.value, withEq(d2->lower.reasons));
            if (d2->hasUpper && (!d1->hasUpper || d2->upper.value < d1->upper.value))
                domains_.addUpperBound(v1, d2->upper.value, withEq(d2->upper.reasons));
        }
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageSquareBound(TheoryLemmaStorage&, TheoryEffort) {
    auto sr = squareBound_.run(normalized_, domains_);
    if (sr.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*sr.conflict);
    }
    if (sr.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown("NIA: square bound reasoning fatal unknown");
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageSumOfSquares(TheoryLemmaStorage&, TheoryEffort) {
    auto ssr = sumOfSquaresBound_.run(normalized_, domains_);
    if (ssr.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*ssr.conflict);
    }
    if (ssr.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown("NIA: sum-of-squares bound reasoning fatal unknown");
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageUnivariate(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    auto ur = univariate_.run(normalized_, domains_, lemmaDb);
    if (ur.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*ur.conflict);
    }
    if (ur.kind == NiaReasoningKind::Lemma) {
        return TheoryCheckResult::mkLemma(*ur.lemma);
    }
    if (ur.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown("NIA: univariate reasoning fatal unknown");
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageAlgebraic(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    auto ar = algebraic_.run(normalized_, domains_, lemmaDb);
    if (ar.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*ar.conflict);
    }
    if (ar.kind == NiaReasoningKind::Lemma) {
        return TheoryCheckResult::mkLemma(*ar.lemma);
    }
    if (ar.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown("NIA: algebraic reasoning fatal unknown");
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageGcdDivisibility(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableGcd_) return std::nullopt;
    auto r = gcdDivisibility_.run(normalized_);
    if (r.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageModular(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableModular_) return std::nullopt;

    // L4.1 — modular warm-start memoization. The modular reasoner has
    // been profiled re-running its full detection (ModGroups, SimpleDefs,
    // CheckEqs, Newton-chain synthesis, Hensel lifting, residue
    // enumeration) every Full-effort cb_check on identical normalized_
    // streams. Skip the re-run when the constraint signature matches the
    // previous call's signature AND the previous result was NoChange.
    //
    // Soundness: NoChange writes no state and emits no verdict; replaying
    // it under unchanged signature is correctness-preserving. Conflicts
    // are NEVER memoized (the solver acts on a conflict by backtracking;
    // a stale conflict on a backtracked-from state would be unsound).
    //
    // Signature: FNV-1a over (poly, rel) pairs in normalized_ order —
    // same convention as the LS warm-start signature. Index order is
    // stable because normalized_ is grown in lockstep with active_ /
    // onBacktrack resizes it from the tail.
    static const bool warmStartEnabled = [] {
        const char* e = std::getenv("XOLVER_NIA_MODULAR_WARM_START");
        return e && *e && *e != '0';
    }();
    auto computeSignature = [&]() -> uint64_t {
        uint64_t h = 1469598103934665603ULL;  // FNV-1a basis
        for (const auto& c : normalized_) {
            h ^= static_cast<uint64_t>(c.poly);
            h *= 1099511628211ULL;
            h ^= static_cast<uint64_t>(c.rel);
            h *= 1099511628211ULL;
        }
        return h;
    };
    if (warmStartEnabled && modularSignatureValid_ && modularLastWasNoChange_) {
        const uint64_t sig = computeSignature();
        if (sig == modularLastSignature_) {
            // Same constraint set, last verdict was NoChange — replay it.
            return std::nullopt;
        }
        // Signature changed: drop cache, fall through to re-run.
        modularSignatureValid_ = false;
    }

    auto r = modularResidue_.run(normalized_);
    if (r.kind == NiaReasoningKind::Conflict) {
        // Don't memoize conflicts (see soundness note above).
        modularSignatureValid_ = false;
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    // NoChange — cache signature for the next call.
    if (warmStartEnabled) {
        modularLastSignature_ = computeSignature();
        modularLastWasNoChange_ = true;
        modularSignatureValid_ = true;
    }
    return std::nullopt;
}

void NiaSolver::setModEqConstFacts(ModEqConstFactList facts) {
    // Track A Phase 1.3 — Solver::Impl hands off facts captured from
    // IntDivModLowerer here. Each fact's `reason` SatLit is still
    // unset (atomization is done after preprocess); the stage method
    // resolves it via TheoryAtomRegistry per call.
    modEqConstFacts_ = std::move(facts);
}

std::optional<TheoryCheckResult> NiaSolver::stageNativeModEqConst(
    TheoryLemmaStorage&, TheoryEffort) {
    // Track A Phase 1.3 — bridge fact list to ModEqConstReasoner.
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NIA_NATIVE_MODEQCONST");
        return e && *e && *e != '0';
    }();
    if (!enabled) return std::nullopt;
    if (modEqConstFacts_.empty()) return std::nullopt;
    if (!registry_) return std::nullopt;

    // Build a per-call snapshot of facts with `reason` resolved via the
    // TheoryAtomRegistry. Skip any fact whose atom is not currently asserted
    // true on the SAT trail.
    ModEqConstFactList active;
    active.reserve(modEqConstFacts_.size());
    for (const auto& src : modEqConstFacts_) {
        auto satVarOpt = registry_->findSatVarByExprId(src.atomExpr);
        if (!satVarOpt) continue;
        SatVar var = *satVarOpt;
        // Need positive polarity asserted (fact `(= (mod x y) c)` is true
        // only when the SAT layer has set the atom to true). The active
        // literal set tracks current-level asserted lits.
        SatLit posLit{var, /*sign=*/false};
        if (!activeSet_.contains(posLit)) continue;
        ModEqConstFact f = src;
        f.reason = posLit;
        active.push_back(std::move(f));
    }
    if (active.empty()) return std::nullopt;

    auto r = modEqConst_.run(active, domains_);
    if (r.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    // DomainUpdated / NoChange both fall through to the next stage.
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageDio(TheoryLemmaStorage&, TheoryEffort) {
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NIA_DIO");
        return e && *e && *e != '0';
    }();
    if (!enabled) return std::nullopt;

    // (A) Lattice-step + bound tightening (arith-dio-tighten). Marshals the live
    // equalities / disequalities / inequalities (normalized_) and the per-variable
    // bounds (domains_, populated by the earlier linear-domain stage) into the
    // shared DioReasoner::tightenConflict — which folds complementary inequality
    // pairs + pinned bounds into the lattice. Refutes the QF_(A)NIA
    // integer-Diophantine cluster (in-de42 etc.) when NIA gets the check.
    {
        std::vector<DioLinForm> cons;
        for (const auto& c : normalized_) {
            if (c.rel != Relation::Eq && c.rel != Relation::Neq &&
                c.rel != Relation::Leq && c.rel != Relation::Geq) continue;
            auto termsOpt = kernel_->terms(c.poly);
            if (!termsOpt) continue;
            DioLinForm f;
            f.cst = 0;
            f.rel = c.rel;
            f.reason = c.reason;
            bool linear = true;
            for (const auto& t : *termsOpt) {
                if (t.powers.empty()) { f.cst += t.coefficient; continue; }
                if (t.powers.size() != 1 || t.powers[0].second != 1) { linear = false; break; }
                f.coeffs.emplace_back(std::string(kernel_->varName(t.powers[0].first)), t.coefficient);
            }
            if (!linear || f.coeffs.empty()) continue;
            cons.push_back(std::move(f));
        }
        std::map<std::string, DioVarBound> bnds;
        for (const auto& [name, dom] : domains_.getAllDomains()) {
            DioVarBound bb;
            if (dom.hasLower) { bb.hasLo = true; bb.lo = dom.lower.value; bb.loReasons = dom.lower.reasons; }
            if (dom.hasUpper) { bb.hasHi = true; bb.hi = dom.upper.value; bb.hiReasons = dom.upper.reasons; }
            bnds.emplace(name, std::move(bb));
        }
        auto conflictOpt = DioReasoner::tightenConflict(cons, bnds);
        if (conflictOpt) return TheoryCheckResult::mkConflict(TheoryConflict{*conflictOpt});
    }

    // (B) Symbolic modular-congruence path (variable-divisor `(mod x y)=c` facts).
    if (modEqConstFacts_.empty() || !registry_ || !coreIr_) return std::nullopt;

    // Build DioCongruences from currently-asserted (mod x m) = c facts:
    //   (mod x m) = c   =>   x ≡ c (mod m)   for a CONSTANT divisor m > 1.
    // (Variable-divisor facts have no constant modulus and are skipped.)
    std::vector<DioCongruence> congs;
    for (const auto& src : modEqConstFacts_) {
        auto satVarOpt = registry_->findSatVarByExprId(src.atomExpr);
        if (!satVarOpt) continue;
        SatLit posLit{*satVarOpt, /*sign=*/false};
        if (!activeSet_.contains(posLit)) continue;

        const auto& xe = coreIr_->get(src.xExpr);
        if (xe.kind != Kind::Variable) continue;
        const auto* nm = std::get_if<std::string>(&xe.payload.value);
        if (!nm) continue;

        const auto& ye = coreIr_->get(src.yExpr);
        if (ye.kind != Kind::ConstInt) continue;  // need a constant modulus
        mpz_class m;
        if (const auto* i = std::get_if<int64_t>(&ye.payload.value)) m = *i;
        else if (const auto* s = std::get_if<std::string>(&ye.payload.value)) m = mpz_class(*s);
        else continue;
        if (m <= 1) continue;

        congs.push_back({kernel_->getOrCreateVar(*nm), src.c, m, posLit});
    }
    if (congs.empty()) return std::nullopt;

    auto r = dio_.run(normalized_, congs);
    if (r.kind == NiaReasoningKind::Conflict)
        return TheoryCheckResult::mkConflict(*r.conflict);
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageGroebner(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableGroebner_) return std::nullopt;
    auto r = groebner_.run(normalized_);
    if (r.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageIcp(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableIcp_) return std::nullopt;
    std::vector<IcpConstraint> cs;
    cs.reserve(normalized_.size());
    for (const auto& c : normalized_) {
        cs.push_back(IcpConstraint{std::nullopt, c.poly, c.rel, c.reason, TheoryId::NIA});
    }
    NiaIcpAdapter adapter(*kernel_, domains_);
    IcpConfig cfg;  // V1 defaults: contract to fixpoint, suggest (not apply) splits
    auto r = adapter.run(cs, cfg);
    if (r.status == IcpStatus::Conflict && r.conflict) {
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageCdcac(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableCdcac_ || normalized_.empty()) return std::nullopt;
#ifndef XOLVER_HAS_LIBPOLY
    return std::nullopt;  // CDCAC requires the libpoly algebra backend
#else
    if (!cdcacCore_) {
        cdcacAlgebra_ = std::make_unique<LibpolyBackend>(kernel_.get());
        cdcacCore_ = std::make_unique<CdcacCore>(kernel_.get(), cdcacAlgebra_.get());
    }

    // Pre-elimination (the lever — CAD is doubly-exponential in #vars): substitute
    // every domain-FIXED variable (lb == ub, derived by the earlier cheap stages)
    // into the constraint polynomials and drop it from the CDCAC variable set, so
    // CDCAC faces fewer variables. SOUND only if the substituted vars' bound-reasons
    // are threaded into any UNSAT conflict (detection-sound ≠ explanation-sound).
    std::unordered_map<std::string, mpz_class> fixedVal;
    std::unordered_map<std::string, std::vector<SatLit>> fixedReasons;
    for (const auto& [name, dom] : domains_.getAllDomains()) {
        if (dom.hasLower && dom.hasUpper && dom.lower.value == dom.upper.value) {
            fixedVal[name] = dom.lower.value;
            std::vector<SatLit>& rs = fixedReasons[name];
            rs.insert(rs.end(), dom.lower.reasons.begin(), dom.lower.reasons.end());
            rs.insert(rs.end(), dom.upper.reasons.begin(), dom.upper.reasons.end());
        }
    }

    // Build CdcacInput from the (substituted) constraints; lexicographic base
    // variable order (deterministic). varOrder excludes fixed vars because they
    // no longer appear in the substituted polynomials.
    CdcacInput input;
    std::unordered_set<std::string> seen;
    std::vector<std::string> varNames;
    std::unordered_set<std::string> usedFixed;  // fixed vars actually substituted
    for (const auto& c : normalized_) {
        PolyId p = c.poly;
        if (!fixedVal.empty()) {
            for (const auto& v : kernel_->variables(p)) {
                auto it = fixedVal.find(v);
                if (it == fixedVal.end()) continue;
                if (auto vid = kernel_->findVar(v)) {
                    if (auto sp = kernel_->substituteRational(p, *vid, mpq_class(it->second))) {
                        p = *sp;
                        usedFixed.insert(v);
                    }
                }
            }
        }
        CdcacConstraint cc;
        cc.poly = p;
        cc.rel = c.rel;
        cc.reason = c.reason;
        input.constraints.push_back(std::move(cc));
        for (const auto& v : kernel_->variables(p)) {
            if (seen.insert(v).second) varNames.push_back(v);
        }
    }
    std::sort(varNames.begin(), varNames.end());
    for (const auto& name : varNames) input.varOrder.push_back(kernel_->getOrCreateVar(name));

    CdcacResult result = cdcacCore_->solve(input);
    switch (result.status) {
        case CdcacStatus::Unsat: {
            // Real-relaxation covering-UNSAT ⇒ integer-UNSAT (ℤⁿ⊆ℝⁿ). CdcacCore
            // already downgrades an uncertified covering to Unknown, so a Unsat
            // reaching here is a trustworthy real empty-covering proof. Thread in
            // the bound-reasons of every fixed var we substituted (a superset is
            // sound; OMITTING one would be a too-strong/false-UNSAT clause).
            std::vector<SatLit> reasons;
            if (result.unsat) reasons = ReasonManager::minimize(result.unsat->covering);
            for (const auto& name : usedFixed) {
                const auto& rs = fixedReasons[name];
                reasons.insert(reasons.end(), rs.begin(), rs.end());
            }
            return TheoryCheckResult::mkConflict(ReasonManager::toConflict(reasons));
        }
        case CdcacStatus::Sat: {
            // CDCAC's sample is over the reals (and over the REDUCED variable set).
            // Accept as an integer model ONLY if every solved coordinate is an exact
            // integer; reattach the fixed vars; then validate over the ORIGINAL
            // normalized_ (invariant 1: never return a raw candidate).
            if (!result.model) return std::nullopt;
            const SamplePoint& s = *result.model;
            IntegerModel im;
            for (size_t i = 0; i < s.varOrder.size() && i < s.values.size(); ++i) {
                const RealAlg& v = s.values[i];
                if (!v.isRational() || v.rational.get_den() != 1) return std::nullopt;
                im[std::string(kernel_->varName(s.varOrder[i]))] = v.rational.get_num();
            }
            for (const auto& [name, val] : fixedVal) im[name] = val;
            if (validator_.validate(im, normalized_) == IntegerModelValidator::Result::Valid) {
                currentModel_ = std::move(im);
                return TheoryCheckResult::consistent();
            }
            return std::nullopt;
        }
        case CdcacStatus::Unknown:
            return std::nullopt;
    }
    return std::nullopt;
#endif
}

std::optional<TheoryCheckResult> NiaSolver::stageProductPositivity(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableRefute_) return std::nullopt;
    auto r = productPositivity_.run(normalized_, domains_);
    if (r.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageInterval(TheoryLemmaStorage&, TheoryEffort) {
    // Interval evaluation (single-variable only, via common framework)
    ReasonedBoxZ box;
    for (const auto& c : normalized_) {
        for (const auto& var : kernel_->variables(c.poly)) {
            if (box.get(var)) continue; // already set
            const IntDomain* d = domains_.getDomain(var);
            if (d && d->hasLower && d->hasUpper) {
                std::vector<SatLit> reasons;
                reasons.insert(reasons.end(), d->lower.reasons.begin(), d->lower.reasons.end());
                reasons.insert(reasons.end(), d->upper.reasons.begin(), d->upper.reasons.end());
                box.set(var, ReasonedInterval{IntervalZ{d->lower.value, d->upper.value}, reasons});
            }
        }
    }
    for (const auto& c : normalized_) {
        IntervalConstraint ic{c.poly, c.rel, c.reason};
        auto ir = intervalEvaluator_.run(ic, box);
        if (ir.status == IntervalEvalStatus::DefinitelyViolated) {
            std::vector<SatLit> lits;
            lits.push_back(c.reason);
            for (const auto& r : ir.usedReasons) {
                lits.push_back(r);
            }
            return TheoryCheckResult::mkConflict(TheoryConflict{lits});
        }
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageLinearization(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    // 9.4: Mirror effective active linear bounds to LIA
    if (pendingLinLemmas_.empty() && registry_ && linAdapter_) {
        std::vector<LinearizerActiveAssignment> laas;
        laas.reserve(trail().size());
        for (const auto& a : trail()) {
            laas.push_back({a.level, a.lit, a.atom, a.value});
        }
        auto mirrorLemmas = linAdapter_->mirrorActiveLinearBounds(laas, TheoryId::LIA);
        for (auto& ml : mirrorLemmas) {
            if (!lemmaDb.contains(ml)) {
                lemmaDb.insertIfNew(ml);
                pendingLinLemmas_.push_back(std::move(ml));
            }
        }
    }

    // 9.5: Incremental linearization for nonlinear constraints
    // V1 limited: abstraction lemma + square nonnegativity only.
    // No McCormick, secant, tangent until LIA aux-var handling is verified.
    //
    // H1 (master 2026-06-01 audit): XOLVER_NIA_SECANT (default-OFF)
    // re-enables the upper-bounding square secant cut for NIA. The cut
    // (x^2 <= ((hi+lo)*x - hi*lo)) over a bounded box is a sound valid
    // linear inequality (cvc5 NLext canonical lemma). It was originally
    // gated off pending LIA aux-var handling; the LIA simplex is now
    // stable (lia P4 incremental-beta shipped), so re-enabling is a
    // candidate ship. NRA's NraLinearizationAdapter already runs with
    // emitSquareSecant=true, so the cut-generator code path is
    // production-validated; only the wire-in is opt-in here.
    if (pendingLinLemmas_.empty() && registry_ && linAdapter_) {
        LinearizationConfig cfg;
        cfg.emitAllMcCormick = true;
        static const bool secantOn = [] {
            const char* e = std::getenv("XOLVER_NIA_SECANT");
            return e && *e && *e != '0';
        }();
        cfg.emitSquareSecant = secantOn;
        cfg.emitSquareTangent = true;
        cfg.emitSquareNonneg = true;
        cfg.maxLemmas = 10;
        cfg.maxCutsPerTerm = 4;

        auto lr = linAdapter_->runLinearizer(normalized_, domains_, lemmaDb, cfg);
        if (lr.status == LinearizationStatus::Lemma) {
            for (auto& item : lr.lemmas) {
                if (!lemmaDb.contains(item.lemma)) {
                    lemmaDb.insertIfNew(item.lemma);
                    pendingLinLemmas_.push_back(std::move(item.lemma));
                    if (item.cacheKey) {
                        linAdapter_->markEmitted(*item.cacheKey);
                    }
                }
            }
        }
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageBoundedEarly(TheoryLemmaStorage&, TheoryEffort) {
    // Phase 3b: early-pipeline placement of the partial bounded
    // enumerator. Reads its own flag XOLVER_NIA_BOUNDED_PARTIAL_EARLY
    // (separate from the late-stage XOLVER_NIA_BOUNDED_PARTIAL — former
    // controls placement, latter algorithm). Sound SAT-finding only;
    // never returns UnsatComplete. On failure, falls through to the
    // rest of the pipeline (so the standard reasoners still get to run).
    static const bool earlyEnabled = [] {
        const char* e = std::getenv("XOLVER_NIA_BOUNDED_PARTIAL_EARLY");
        return e && *e && *e != '0';
    }();
    if (!earlyEnabled) return std::nullopt;
    // Reuse the same algorithm; differs only in pipeline position.
    // Phase L1 step 3 — LS feedback hint (XOLVER_NIA_LS_FEEDBACK=1,
    // default-OFF). The LS context's bestAssignment (when present) is
    // tried as the FIRST candidate before cartesian enumeration. Sound:
    // validator-gated like every other candidate.
    static const bool lsFeedback = [] {
        const char* e = std::getenv("XOLVER_NIA_LS_FEEDBACK");
        return e && *e && *e != '0';
    }();
    const IntegerModel* hint = nullptr;
    if (lsFeedback) {
        const auto& ctx = localSearch_.lsContext();
        if (!ctx.bestAssignment.empty()) hint = &ctx.bestAssignment;
    }
    auto br = bounded_.solvePartialWithHint(normalized_, domains_, validator_, hint);
    if (br.status == BoundedSolveStatus::Sat) {
        currentModel_ = br.model;
        return TheoryCheckResult::consistent();
    }
    // Any other status — fall through to the regular pipeline.
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageBounded(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    auto allVars = collectVars(normalized_, *kernel_);
    bool allFinite = domains_.allFinite(allVars);
    if (allFinite) {
        // Domain is finite: bounded solver is authoritative; skip linear lemmas
        pendingLinLemmas_.clear();
        auto br = bounded_.solve(normalized_, domains_, validator_, lemmaDb);
        if (br.status == BoundedSolveStatus::Sat) {
            currentModel_ = br.model;
            return TheoryCheckResult::consistent();
        }
        if (br.status == BoundedSolveStatus::UnsatComplete) {
            return TheoryCheckResult::mkConflict(*br.conflict);
        }
        // UnknownBudget / UnknownUnsupported: continue pipeline
    } else {
        // Phase 3a (XOLVER_NIA_BOUNDED_PARTIAL, default-OFF). When the full
        // domain isn't finite (some unbounded vars), try the partial
        // enumerator: enumerate the tightly-bounded subset × small guess
        // sets for unbounded vars, validate each candidate against the
        // ORIGINAL constraints. Sound SAT-finding only — UnsatComplete is
        // never returned from this path (unbounded search space is not
        // exhausted).
        static const bool partialEnabled = [] {
            const char* e = std::getenv("XOLVER_NIA_BOUNDED_PARTIAL");
            return e && *e && *e != '0';
        }();
        if (partialEnabled) {
            // Phase L1 step 3 — LS feedback hint (XOLVER_NIA_LS_FEEDBACK=1,
    // default-OFF). The LS context's bestAssignment (when present) is
    // tried as the FIRST candidate before cartesian enumeration. Sound:
    // validator-gated like every other candidate.
    static const bool lsFeedback = [] {
        const char* e = std::getenv("XOLVER_NIA_LS_FEEDBACK");
        return e && *e && *e != '0';
    }();
    const IntegerModel* hint = nullptr;
    if (lsFeedback) {
        const auto& ctx = localSearch_.lsContext();
        if (!ctx.bestAssignment.empty()) hint = &ctx.bestAssignment;
    }
    auto br = bounded_.solvePartialWithHint(normalized_, domains_, validator_, hint);
            if (br.status == BoundedSolveStatus::Sat) {
                currentModel_ = br.model;
                return TheoryCheckResult::consistent();
            }
            // Any other status (UnknownUnsupported / UnknownBudget) — fall
            // through to the next pipeline stage.
        }
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageBitBlastEarly(TheoryLemmaStorage&, TheoryEffort) {
    // DEFAULT-ON (2026-06-05): run the WHOLE-problem bit-blast early — while the
    // variable box is still free — instead of leaving it to the FULL-effort
    // nia.bit-blast which fires once the SAT search has PINNED the small bounded
    // vars to a specific (often wrong) branch. On a box-INCOMPLETE pinned branch
    // (unbounded beta/gamma, e.g. the GrandProduct prime-field grand product) the
    // late per-branch path cannot prove the branch UNSAT, so it escalates width
    // K=2→128 and allocates ~3.3 GB before the firewall — a real OOM bug, NOT a
    // resource wall (z3 solves the same case instantly). Searching the whole free
    // problem once keeps the encoding bounded (~0.6 GB) and lets the SAT solver
    // explore all branches together. This is an ALGORITHMIC fix (search strategy),
    // not a width/budget cap. The >=50 active-constraint gate below preserves the
    // small-case behavior (BB_EARLY's per-call cost regressed tiny UNSAT cases
    // before that gate). Opt-out: XOLVER_NIA_BB_EARLY=0.
    static const bool earlyEnabled = [] {
        const char* e = std::getenv("XOLVER_NIA_BB_EARLY");
        return !e || (*e && *e != '0');   // default ON; only "0" disables
    }();
    if (!earlyEnabled) return std::nullopt;
    if (!enableBitBlast_) return std::nullopt;
    if (std::getenv("XOLVER_NIA_NO_BITBLAST")) return std::nullopt;
    // Array-combination gate: when the problem contains array terms (Store/Select),
    // the array-read results are EUF-managed shared terms abstracted into the NIA
    // constraints as opaque vars. Bit-blasting those constraints is wasteful (it
    // was the ~1s/call hot stage on the array-combination GrandProduct, confirmed
    // via ARITH_STAGE_PROF) and can mislead (the bit-blast model ignores the EUF
    // array axioms). The combination + other reasoner stages own these. Opt-out
    // XOLVER_NIA_BB_ARRAY=1. (Verified: sum10 etc. still solve without bit-blast.)
    if (bbArrayGate_ < 0) {
        bbArrayGate_ = 0;
        if (coreIr_ && !std::getenv("XOLVER_NIA_BB_ARRAY")) {
            ExprId n = static_cast<ExprId>(coreIr_->size());
            for (ExprId e = 0; e < n; ++e) {
                Kind k = coreIr_->get(e).kind;
                if (k == Kind::Store || k == Kind::Select) { bbArrayGate_ = 1; break; }
            }
        }
    }
    if (bbArrayGate_ == 1) return std::nullopt;
    // H3 size-gate: BB_EARLY's per-call encoding+SAT cost is heavy
    // (~5-6s on SAT14-class with 600+ active polynomial constraints).
    // On small NIA cases (~1-10 active constraints) the upstream
    // reasoning stages decide the verdict for free, and BB_EARLY's
    // overhead pushes them past the per-case timeout. Local NIA reg
    // verified this: BB_EARLY ON regressed 3 small UNSAT cases (nia_025,
    // nia_056, nia_090) from unsat to unknown, and 3 to TIMEOUT.
    // Threshold: require >= 50 active normalized constraints, the
    // SAT14-pattern lower bound. Tunable via XOLVER_NIA_BB_EARLY_MIN_ACTIVE.
    static const size_t minActive = [] {
        if (const char* e = std::getenv("XOLVER_NIA_BB_EARLY_MIN_ACTIVE"))
            return static_cast<size_t>(std::atol(e));
        return static_cast<size_t>(50);
    }();
    if (normalized_.size() < minActive) return std::nullopt;
    static const bool h3Diag = std::getenv("XOLVER_NIA_BB_ENTRY_DIAG") != nullptr;
    if (h3Diag) {
        static thread_local long earlyCount = 0;
        ++earlyCount;
        if ((earlyCount & 0xff) == 1 || earlyCount < 8) {
            std::fprintf(stderr,
                "[BB-EARLY] call=%ld active=%zu normalized=%zu\n",
                earlyCount, active_.size(), normalized_.size());
        }
    }
    // Dedup re-blasts of the same free problem (see bbEarlyUnkSize_). If the last
    // blast at this active-constraint size returned UNKNOWN, the free problem is
    // unchanged and a re-blast just burns seconds (00314 80x/11s; a UFDTNIA
    // 4x/14.6s) — skip it. Opt-out XOLVER_NIA_BB_EARLY_NODEDUP=1.
    static const bool bbEarlyDedup =
        std::getenv("XOLVER_NIA_BB_EARLY_NODEDUP") == nullptr;
    if (bbEarlyDedup && bbEarlyUnkSize_ == normalized_.size())
        return std::nullopt;
    // The bit-blast solver respects its own gate/iteration env caps
    // (XOLVER_NIA_BITBLAST_MAX_ITERS / MAX_BITWIDTH / GATE_BUDGET /
    // CONFLICTS). For early-stage operation users typically pair this
    // flag with tighter caps so Standard-effort cb_propagate overhead
    // stays bounded — same idiom as XOLVER_NIA_LS_EARLY_BUDGET_MS.
    auto res = bitBlast_.solve(normalized_, domains_, validator_);
    switch (res.status) {
        case bitblast::BitBlastResult::Status::Sat:
            currentModel_ = res.model;
            return TheoryCheckResult::consistent();
        case bitblast::BitBlastResult::Status::UnsatComplete:
            return TheoryCheckResult::mkConflict(*res.conflict);
        case bitblast::BitBlastResult::Status::Unknown:
            if (bbEarlyDedup) bbEarlyUnkSize_ = normalized_.size();
            return std::nullopt;
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageBitBlast(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableBitBlast_) return std::nullopt;
    if (std::getenv("XOLVER_NIA_NO_BITBLAST")) return std::nullopt;  // diag/A-B: isolate non-bit-blast NIA reasoning
    // H3 (master 2026-06-01) entry counter: confirm whether bit-blast
    // actually fires on SAT14-class inputs before the run TOs upstream.
    static const bool h3Diag = std::getenv("XOLVER_NIA_BB_ENTRY_DIAG") != nullptr;
    if (h3Diag) {
        static thread_local long bbEntryCount = 0;
        ++bbEntryCount;
        if ((bbEntryCount & 0xff) == 1 || bbEntryCount < 8) {
            std::fprintf(stderr,
                "[BB-ENTRY] call=%ld active=%zu normalized=%zu\n",
                bbEntryCount, active_.size(), normalized_.size());
        }
    }
    auto res = bitBlast_.solve(normalized_, domains_, validator_);
    switch (res.status) {
        case bitblast::BitBlastResult::Status::Sat:
            currentModel_ = res.model;
            return TheoryCheckResult::consistent();
        case bitblast::BitBlastResult::Status::UnsatComplete:
            return TheoryCheckResult::mkConflict(*res.conflict);
        case bitblast::BitBlastResult::Status::Unknown:
            return std::nullopt;
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult>
NiaSolver::stageEscalatingBounded(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    (void)lemmaDb;
    static const bool enabled =
        env::paramInt("XOLVER_NIA_BOUNDED_ESCALATE", 1) != 0;
    if (!enabled) return std::nullopt;
    (void)effort;  // Full-effort-only is enforced by the addFull() registration.
    if (!coreIr_) return std::nullopt;  // need the original formula for AMV.
    if (normalized_.empty()) return std::nullopt;

    // Detect vars with a finite lower bound but no upper bound. These are
    // exactly the inputs BoundedNiaSolver can't enumerate today (it bails to
    // UnknownUnsupported in solve()). Be conservative: if there are vars with
    // no domain info OR unbounded below, skip — those are outside this
    // stage's sound lane.
    auto allVars = collectVars(normalized_, *kernel_);
    std::vector<std::string> vars(allVars.begin(), allVars.end());
    std::sort(vars.begin(), vars.end()); // determinism
    std::vector<std::pair<mpz_class, mpz_class>> ranges; // (lo, hi) per var
    ranges.reserve(vars.size());
    bool anyUnboundedAbove = false;
    for (const auto& v : vars) {
        const IntDomain* d = domains_.getDomain(v);
        if (!d) return std::nullopt;
        if (!d->hasLower) return std::nullopt;   // unbounded below — out of lane
        mpz_class lo = d->lower.value;
        if (d->hasUpper) {
            // already capped — keep the existing window
            ranges.push_back({lo, d->upper.value});
        } else {
            ranges.push_back({lo, lo});          // placeholder; widened per k
            anyUnboundedAbove = true;
        }
    }
    if (!anyUnboundedAbove) return std::nullopt; // nia.bounded covers this.
    (void)effort;

    // Cap on per-iteration enumeration size (autotunable knob, iter#5 hoist).
    // STRUCTURAL bound — no artificial k cap; the loop terminates when the
    // augmented box exceeds this threshold for any k.
    const long enumThreshold =
        env::paramLong("XOLVER_NIA_BOUNDED_ENUM_THRESHOLD", 10000);

    // Collect bool AND array vars referenced in the ORIGINAL formula.
    //   - Bool vars: BoolSubterm Purifier introduces `boolpur_K` fresh bool
    //     vars to name complex subexpressions; AMV cannot evaluate them
    //     without a BoolAssignment, so every candidate goes Indeterminate.
    //     We enumerate ALL polarity combos.
    //   - Array vars: QF_ANIA / QF_AUFNIA cases declare arrays (e.g.
    //     `(declare-fun start () (Array Int Int))`); AMV's Select / Store
    //     return Indeterminate when the base array var has no interp. We
    //     supply each Array var with a baseline ConstArray (default token
    //     "#n:0") so the store-chain accumulates correctly. SOUND: the
    //     baseline is a candidate guess — if the SAT witness needs different
    //     base values, AMV will reject this combo and we miss the witness,
    //     never claim a wrong SAT.
    std::set<std::string> boolVarSet;
    std::set<std::string> arrayVarSet;
    {
        std::vector<ExprId> wstack;
        std::unordered_set<ExprId> wseen;
        for (ExprId a : coreIr_->assertions()) wstack.push_back(a);
        const SortId boolSort = coreIr_->boolSortId();
        while (!wstack.empty()) {
            ExprId e = wstack.back(); wstack.pop_back();
            if (e == NullExpr || e >= coreIr_->size()) continue;
            if (!wseen.insert(e).second) continue;
            const auto& n = coreIr_->get(e);
            if (n.kind == Kind::Variable) {
                if (auto* nm = std::get_if<std::string>(&n.payload.value)) {
                    if (n.sort == boolSort) {
                        boolVarSet.insert(*nm);
                    } else if (coreIr_->arraySortParams(n.sort)) {
                        arrayVarSet.insert(*nm);
                    }
                }
            }
            for (ExprId c : n.children) wstack.push_back(c);
        }
    }
    std::vector<std::string> boolVars(boolVarSet.begin(), boolVarSet.end());
    std::sort(boolVars.begin(), boolVars.end());
    const size_t nBoolVars = boolVars.size();
    // STRUCTURAL skip: 2^nBoolVars must fit in long enumeration. With
    // enumThreshold=10000 default, 2^13 = 8192 already eats most of it.
    // We don't add an artificial cap, but skip the bool-enum entirely if
    // 2^nBoolVars exceeds the threshold (sound — bool vars left Indeterminate
    // means more candidates get rejected, not fewer; we miss SAT, we don't
    // claim UNSAT).
    long boolCombo = 1;
    for (size_t i = 0; i < nBoolVars; ++i) {
        if (boolCombo > enumThreshold) { boolCombo = -1; break; }
        boolCombo *= 2;
    }
    if (boolCombo < 0) return std::nullopt;

    // AMV input scaffold reused across candidates (zero-alloc inner loop).
    ArithModelValidator::NumAssignment num;
    num.reserve(vars.size());
    ArithModelValidator::BoolAssignment bools;
    bools.reserve(nBoolVars);
    // Array baseline: each Array var gets a ConstArray with default token
    // "#n:0" (matches AMV's auto-token form for the rational 0; see
    // ArithModelValidator.cpp::asToken at line 80). Built ONCE before the
    // enumeration loop — same baseline for every (int × bool) combo, since
    // the formula's stores accumulate as overrides on top.
    ArithModelValidator::ArrayAssignment arrAsg;
    ArithModelValidator::TokenAssignment tokAsg;  // empty — Number→token auto-converts
    if (!arrayVarSet.empty()) {
        arrAsg.reserve(arrayVarSet.size());
        for (const auto& aname : arrayVarSet) {
            TheorySolver::TheoryModel::ArrayInterp interp;
            interp.defaultVal = "#n:0";
            // entries empty: no overrides on the baseline
            arrAsg.emplace(aname, std::move(interp));
        }
    }

    // Escalate width = 2^k - 1 on UNBOUNDED vars; keep bounded vars' ranges
    // intact. Compute totalSize first; if > threshold, stop escalating.
    for (int k = 1; ; ++k) {
        mpz_class widthMinus1 = (mpz_class(1) << k) - 1; // 2^k - 1

        // Build per-var (lo, hi) for THIS k, and compute totalSize.
        std::vector<std::pair<mpz_class, mpz_class>> kRanges = ranges;
        mpz_class totalSize = 1;
        bool overBudget = false;
        for (size_t i = 0; i < vars.size(); ++i) {
            const IntDomain* d = domains_.getDomain(vars[i]);
            if (d && !d->hasUpper) {
                kRanges[i] = {kRanges[i].first, kRanges[i].first + widthMinus1};
            }
            mpz_class span = kRanges[i].second - kRanges[i].first + 1;
            if (span <= 0) { overBudget = true; break; }
            totalSize *= span;
            if (totalSize > enumThreshold) { overBudget = true; break; }
        }
        if (overBudget) break;
        // Combined per-k cost: int product × 2^nBoolVars. Skip k if combined
        // is over threshold (sound — skipping cases that exhaust budget is
        // not a wrong-UNSAT, just an unrecovered SAT chance).
        if (nBoolVars > 0) {
            mpz_class combined = totalSize * boolCombo;
            if (combined > enumThreshold) break;
        }

        // Cartesian-product enumeration. For each int-candidate × bool-
        // candidate, validate via ArithModelValidator against the ORIGINAL
        // coreIr_ assertions — pattern mirrors stageLocalSearchBoolExtend
        // but extended to ENUMERATE bool var polarities (boolpur_K Tseitin
        // proxies introduced by the purifier). SOUND for SAT: a model that
        // satisfies the ORIGINAL boolean+arith formula is a sound SAT
        // witness regardless of the partial constraint subset in normalized_.
        const size_t N = vars.size();
        std::vector<mpz_class> cur(N);
        for (size_t i = 0; i < N; ++i) cur[i] = kRanges[i].first;
        while (true) {
            // Build NumAssignment from `cur`.
            num.clear();
            for (size_t i = 0; i < N; ++i) {
                num.emplace(vars[i], mpq_class(cur[i]));
            }
            // Iterate all 2^nBoolVars polarity combos. With nBoolVars=0 the
            // loop body runs exactly once with empty BoolAssignment.
            for (long bmask = 0; bmask < boolCombo; ++bmask) {
                bools.clear();
                for (size_t i = 0; i < nBoolVars; ++i) {
                    bools.emplace(boolVars[i], ((bmask >> i) & 1) != 0);
                }
                // Use the array-aware ctor when the formula has Array vars,
                // so AMV's Select / Store paths can evaluate.
                std::unique_ptr<ArithModelValidator> amvPtr;
                if (!arrayVarSet.empty()) {
                    amvPtr = std::make_unique<ArithModelValidator>(
                        *coreIr_, num, bools, arrAsg, tokAsg);
                } else {
                    amvPtr = std::make_unique<ArithModelValidator>(
                        *coreIr_, num, bools);
                }
                if (amvPtr->validate(coreIr_->assertions()) ==
                    ArithModelValidator::Verdict::Satisfied) {
                    // Materialize as NIA's currentModel_ — IntegerModel is
                    // a map<string, mpz_class>, same shape as `cur`. Bool
                    // proxies stay implicit in the model — the solver caller
                    // (Solver::Impl) re-validates the full model via the
                    // boundary validator with the SAT-layer's own bool
                    // assignments, so the eventual SAT verdict is
                    // double-checked.
                    IntegerModel model;
                    for (size_t i = 0; i < N; ++i) model[vars[i]] = cur[i];
                    currentModel_ = std::move(model);
                    return TheoryCheckResult::consistent();
                }
            }
            // Increment cur in odometer order.
            size_t j = 0;
            while (j < N) {
                ++cur[j];
                if (cur[j] <= kRanges[j].second) break;
                cur[j] = kRanges[j].first;
                ++j;
            }
            if (j == N) break; // exhausted
        }
        // No SAT in this k's box; escalate (any unbounded var grows).
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageLocalSearch(TheoryLemmaStorage&, TheoryEffort) {
    // HYB-X partition-hint wire-up (default-OFF).
    {
        static const bool partHint = std::getenv("XOLVER_NIA_LS_PARTITION_HINT") != nullptr;
        if (partHint && !normalized_.empty()) {
            VariablePartition vp(*kernel_);
            auto pr = vp.partition(normalized_, domains_, 32);
            localSearch_.setPartitionHint(pr);
        }
    }
    // Local search SAT finder (try before emitting pending linear lemmas)
    if (auto model = localSearch_.tryFindModel(normalized_, domains_)) {
        if (validator_.validate(*model, normalized_) == IntegerModelValidator::Result::Valid) {
            currentModel_ = *model;
            return TheoryCheckResult::consistent();
        }
    }
    return std::nullopt;
}

// LS-SMART-Z5 (master 2026-06-02) — Boolean-extend re-validate.
//
// stageLocalSearch's gate accepts only assignments where every active atom
// (the SAT layer's currently-asserted polynomial-atom truth assignment)
// is satisfied. But CaDiCaL's branch is one of many consistent Boolean
// valuations of the CNF abstraction; LS may find an integer assignment m
// that violates a few active atoms YET satisfies the ORIGINAL FORMULA
// under a different Boolean valuation B' (the formula's disjunctive
// structure tolerates the mismatch). Throwing m away is over-strict.
//
// Z5 walks the original CoreIr formula under m via ArithModelValidator
// (the exact arithmetic + Boolean structure evaluator used by Solver::Impl
// at the top-level soundness gate). If Satisfied → return Sat. Sound: AMV
// is exact; SAT verdicts are never claimed on weaker evidence than what
// Solver::Impl would itself accept. UNSAT is never claimed from this path.
//
// Default-OFF, Full-effort only via addFull. Flag XOLVER_NIA_LS_BOOL_EXTEND.
std::optional<TheoryCheckResult>
NiaSolver::stageLocalSearchBoolExtend(TheoryLemmaStorage&, TheoryEffort) {
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NIA_LS_BOOL_EXTEND");
        return e && *e && *e != '0';
    }();
    if (!enabled || coreIr_ == nullptr) return std::nullopt;

    // Pull LS's best-effort partial assignment from the warm-start context.
    // bestAssignment may be empty (LS never ran, or warm-start disabled).
    const auto& best = localSearch_.lsContext().bestAssignment;
    if (best.empty()) return std::nullopt;

    // Translate the integer model into ArithModelValidator's numeric
    // assignment (mpq over var names).
    ArithModelValidator::NumAssignment num;
    num.reserve(best.size());
    for (const auto& kv : best) {
        num.emplace(kv.first, mpq_class(kv.second));
    }

    // Bool var enumeration (iter#12 finding): the BoolSubterm Purifier
    // introduces fresh `boolpur_K` bool vars to name complex subexpressions.
    // AMV cannot evaluate them without a BoolAssignment, so the formula
    // returned Indeterminate even when LS's bestAssignment was the genuine
    // SAT witness. Collect bool vars from coreIr_ and enumerate every
    // polarity combo. SOUND: each combo is independently AMV-validated;
    // Satisfied requires the FULL formula to evaluate true.
    std::set<std::string> boolVarSet;
    {
        std::vector<ExprId> wstack;
        std::unordered_set<ExprId> wseen;
        for (ExprId a : coreIr_->assertions()) wstack.push_back(a);
        const SortId boolSort = coreIr_->boolSortId();
        while (!wstack.empty()) {
            ExprId e = wstack.back(); wstack.pop_back();
            if (e == NullExpr || e >= coreIr_->size()) continue;
            if (!wseen.insert(e).second) continue;
            const auto& n = coreIr_->get(e);
            if (n.kind == Kind::Variable && n.sort == boolSort) {
                if (auto* nm = std::get_if<std::string>(&n.payload.value)) {
                    boolVarSet.insert(*nm);
                }
            }
            for (ExprId c : n.children) wstack.push_back(c);
        }
    }
    std::vector<std::string> boolVars(boolVarSet.begin(), boolVarSet.end());
    std::sort(boolVars.begin(), boolVars.end());
    const size_t nBoolVars = boolVars.size();
    // Structural bound: 2^nBoolVars must fit a long without overflow AND not
    // exceed ENUMERATION_THRESHOLD. Cases with too many bool vars fall through.
    const long enumThreshold =
        env::paramLong("XOLVER_NIA_BOUNDED_ENUM_THRESHOLD", 10000);
    long boolCombo = 1;
    for (size_t i = 0; i < nBoolVars; ++i) {
        if (boolCombo > enumThreshold) return std::nullopt;
        boolCombo *= 2;
    }

    ArithModelValidator::BoolAssignment bools;
    bools.reserve(nBoolVars);
    for (long bmask = 0; bmask < boolCombo; ++bmask) {
        bools.clear();
        for (size_t i = 0; i < nBoolVars; ++i) {
            bools.emplace(boolVars[i], ((bmask >> i) & 1) != 0);
        }
        ArithModelValidator amv(*coreIr_, num, bools);
        if (amv.validate(coreIr_->assertions()) ==
            ArithModelValidator::Verdict::Satisfied) {
            // Materialize as the NIA currentModel_ for the caller.
            currentModel_ = best;
            return TheoryCheckResult::consistent();
        }
    }
    return std::nullopt;
}

// HYB-3 (master 2026-06-02): hybrid BB-enumerate-B + LS-probe-U.
// Strategy for SAT14-style cases per H5 finding (|B| ~5%, |U| ~95%):
// enumerate K random samples of bounded vars within their boxes; for
// each B-sample, override DomainStore for those vars to a singleton
// {value} and run a tight-budget LS on the unbounded vars. Validate
// any Sat candidate against the original constraints.
//
// Soundness: every returned Sat is IntegerModelValidator-gated against
// normalized_. UNSAT is never claimed (LS heuristic; BB sub-call too
// short for completeness). HYB-3 is purely a SAT-finder.
//
// Flag: XOLVER_NIA_HYB_BB_LS (default-OFF).
// Tunables:
//   XOLVER_NIA_HYB_BB_LS_K (default 5): B-samples to try per stage call
//   XOLVER_NIA_HYB_BB_LS_PROBE_MS (default 500): per-LS-probe budget
std::optional<TheoryCheckResult> NiaSolver::stageHybridBbLs(TheoryLemmaStorage&, TheoryEffort) {
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NIA_HYB_BB_LS");
        return e && *e && *e != '0';
    }();
    if (!enabled) return std::nullopt;
    if (normalized_.empty()) return std::nullopt;

    // Partition the variables; only proceed when the case matches the
    // SAT14 pattern (small B, large U).
    VariablePartition vp(*kernel_);
    auto pr = vp.partition(normalized_, domains_, 32);
    if (pr.totalVars() == 0) return std::nullopt;
    // Gate: at most 10 bounded vars; unbounded count at least 3x bounded.
    static const size_t maxB = static_cast<size_t>(
        env::paramLong("XOLVER_NIA_HYB_BB_LS_MAX_B", 10));
    if (pr.boundedCount() == 0 || pr.boundedCount() > maxB) return std::nullopt;
    if (pr.unboundedCount() < pr.boundedCount() * 3) return std::nullopt;

    // K = number of random B-samples to try.
    static const int K = env::paramInt("XOLVER_NIA_HYB_BB_LS_K", 5);
    static const long probeMs =
        env::paramLong("XOLVER_NIA_HYB_BB_LS_PROBE_MS", 500);

    // For each B-sample: clone DomainStore, restrict bounded vars to
    // their sample value (pinned), and run LS on the modified store.
    // Deterministic RNG seeded once per process.
    static thread_local std::mt19937_64 rng(0xC4DCAC1234567ULL);

    long origBudget = 0;
    // We can't read the LS's private budget; we set ours and restore.
    // The set/get asymmetry is acceptable — probe budget is local-scoped.
    (void)origBudget;
    localSearch_.setBudgetMs(probeMs);

    for (int k = 0; k < K; ++k) {
        DomainStore subset = domains_;  // deep-copy current store
        // Sample each bounded var.
        for (const auto& bvar : pr.bounded) {
            const auto& info = pr.info.at(bvar);
            // Random in [lower, upper].
            mpz_class span = info.upper - info.lower;
            mpz_class pick;
            if (span <= 0) pick = info.lower;
            else {
                uint64_t r = rng();
                // Use modular reduction; span+1 is the inclusive range size.
                mpz_class spanInc = span + 1;
                mpz_class rmod = mpz_class(static_cast<unsigned long>(r));
                rmod %= spanInc;
                pick = info.lower + rmod;
            }
            // Pin via a finite-set singleton (overrides bounds).
            std::set<mpz_class> singleton{pick};
            subset.restrictToFiniteSet(bvar, singleton, SatLit::positive(0));
        }
        // Run LS on the restricted store.
        auto model = localSearch_.tryFindModel(normalized_, subset);
        if (model && validator_.validate(*model, normalized_) ==
                         IntegerModelValidator::Result::Valid) {
            currentModel_ = *model;
            return TheoryCheckResult::consistent();
        }
    }
    return std::nullopt;
}

// LBBB Phase 2 — stageBoundedBitBlast. After LS has failed (per
// localSearch_.hasFailed()), bit-blast over the box LS visited,
// extended by a buffer. Validate any Sat against the ORIGINAL NIA
// constraints; UNSAT verdict from BB is treated as Unknown (only
// the BOX is searched, not the full integer space). Default-OFF
// (XOLVER_NIA_LBBB), Full-effort only via addFull registration.
std::optional<TheoryCheckResult> NiaSolver::stageBoundedBitBlast(TheoryLemmaStorage&, TheoryEffort) {
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NIA_LBBB");
        return e && *e && *e != '0';
    }();
    if (!enabled) return std::nullopt;
    if (!enableBitBlast_) return std::nullopt;
    if (std::getenv("XOLVER_NIA_NO_BITBLAST")) return std::nullopt;
    if (normalized_.empty()) return std::nullopt;
    // Gate: LS must have run AND failed. Otherwise BB would just be
    // a redundant copy of stageBitBlast — we want LBBB to fire only
    // on the box LS converged toward.
    if (!localSearch_.hasFailed()) return std::nullopt;
    const auto& mins = localSearch_.trackedMin();
    const auto& maxs = localSearch_.trackedMax();
    if (mins.empty() || maxs.empty()) return std::nullopt;

    // Build a fresh DomainStore restricted to the LS-visited box +
    // buffer. For each tracked var v: [min - buffer, max + buffer]
    // where buffer = max(10, range * 0.1).
    DomainStore subset = domains_;  // deep-copy
    SatLit dummyReason = SatLit::positive(0);
    for (const auto& [v, lo] : mins) {
        auto mit = maxs.find(v);
        if (mit == maxs.end()) continue;
        const mpz_class& hi = mit->second;
        mpz_class range = hi - lo;
        mpz_class buffer = range / 10;
        if (buffer < 10) buffer = 10;
        mpz_class bbLo = lo - buffer;
        mpz_class bbHi = hi + buffer;
        // Intersect with any existing DomainStore bounds.
        subset.addLowerBound(v, bbLo, dummyReason);
        subset.addUpperBound(v, bbHi, dummyReason);
    }
    // Run BitBlast on the restricted box.
    auto res = bitBlast_.solve(normalized_, subset, validator_);
    if (res.status == bitblast::BitBlastResult::Status::Sat) {
        // Validate against ORIGINAL constraints (not the box-bounded
        // subset). LBBB soundness gate: the box restriction was
        // heuristic, so a BB-SAT model must satisfy the unrestricted
        // formula to count.
        if (validator_.validate(res.model, normalized_) ==
            IntegerModelValidator::Result::Valid) {
            currentModel_ = res.model;
            return TheoryCheckResult::consistent();
        }
        // BB found a model in the bounded box, but it doesn't satisfy
        // the original — drop and fall through.
        return std::nullopt;
    }
    // BB returned UNSAT (within the bounded box) or Unknown — both
    // are inconclusive for LBBB. Box might be too small; main pipeline
    // can decide. Never claim UNSAT here.
    return std::nullopt;
}

// HYB-2 (post-Smart-LS). For ITS-like partitions (|B| >= |U|), LS
// has done the U-search and recorded per-var bounds. Pin U vars at
// the midpoint of their LS-visited range via DomainStore singletons,
// then run BitBlast on the residual (which now has only B-free vars,
// plus the pinned-U linear influence factored in). Validate against
// the original NIA formula.
std::optional<TheoryCheckResult> NiaSolver::stageHybridLsBb(TheoryLemmaStorage&, TheoryEffort) {
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NIA_HYB_LS_BB");
        return e && *e && *e != '0';
    }();
    if (!enabled) return std::nullopt;
    if (!enableBitBlast_) return std::nullopt;
    if (std::getenv("XOLVER_NIA_NO_BITBLAST")) return std::nullopt;
    if (normalized_.empty()) return std::nullopt;

    VariablePartition vp(*kernel_);
    auto pr = vp.partition(normalized_, domains_, 32);
    if (pr.totalVars() == 0) return std::nullopt;
    // Gate: B-dominant partition (otherwise HYB-3 / LBBB are better).
    if (pr.unboundedCount() == 0 || pr.boundedCount() < pr.unboundedCount()) {
        return std::nullopt;
    }
    // Read LS-tracked bounds (LBBB Phase 1 prerequisite).
    const auto& mins = localSearch_.trackedMin();
    const auto& maxs = localSearch_.trackedMax();
    if (mins.empty() || maxs.empty()) return std::nullopt;

    DomainStore subset = domains_;
    SatLit dummyReason = SatLit::positive(0);
    bool pinnedAny = false;
    for (const auto& u : pr.unbounded) {
        auto miIt = mins.find(u);
        auto mxIt = maxs.find(u);
        if (miIt == mins.end() || mxIt == maxs.end()) continue;
        mpz_class mid = (miIt->second + mxIt->second) / 2;
        std::set<mpz_class> singleton{mid};
        subset.restrictToFiniteSet(u, singleton, dummyReason);
        pinnedAny = true;
    }
    if (!pinnedAny) return std::nullopt;

    auto res = bitBlast_.solve(normalized_, subset, validator_);
    if (res.status == bitblast::BitBlastResult::Status::Sat) {
        if (validator_.validate(res.model, normalized_) ==
            IntegerModelValidator::Result::Valid) {
            currentModel_ = res.model;
            return TheoryCheckResult::consistent();
        }
    }
    return std::nullopt;
}

// Farkas-Or Phase 4: NiaSolver stage that runs the full
// detector → CSP → assembler → ArithModelValidator pipeline.
//
// Soundness: every SAT verdict here is gated by ArithModelValidator
// against the ORIGINAL coreIr_ assertions. Never returns UNSAT —
// failed CSP / failed validation falls through to the rest of the
// pipeline.
//
// PROMOTED default-ON (2026-06-08): the bounded-B Farkas refutation solves
// VeryMax/Stroeder QF_NIA UNSAT the rest of the pipeline cannot (+11/51 small
// cases measured, 0-unsound), and on non-Farkas inputs the detector bails after
// one O(tree) scan (good()==false → nullopt below). No flag — a good lever
// belongs on the default path, not gated. Full-effort only.
std::optional<TheoryCheckResult>
NiaSolver::stageFarkasOr(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    if (coreIr_ == nullptr) return std::nullopt;

    // Memoize the detector profile + support table across stage calls.
    // The CoreIr doesn't change during the check loop, so we can build
    // once. With residual co-var grid enumeration this is the dominant
    // cost (Stroeder p21258: ~100ms first time, 0ms thereafter).
    static thread_local const CoreIr* cachedIr = nullptr;
    static thread_local farkas::FarkasProfile cachedProfile;
    static thread_local farkas::SupportTable cachedTable;
    if (cachedIr != coreIr_) {
        farkas::FarkasOrDetector det(*coreIr_);
        cachedProfile = det.detect();
        if (!cachedProfile.good()) {
            cachedIr = coreIr_;
            cachedTable = farkas::SupportTable{};
            return std::nullopt;
        }
        farkas::FarkasOrSolver solverBuild(*coreIr_);
        // Cap on the B cartesian product (number of bounded-tuple
        // points the table-builder will enumerate). 500 was the
        // initial conservative pick that floored p21258 (~81 tuples)
        // while skipping p20185-class cases that other NIA stages
        // solve fast. Larger Stroeder cases (Ex2.11 p21280+, 4Nested)
        // have 4+ Or-blocks with 7-λ branches and a denser bounded
        // domain — their B-product runs into the thousands. Bump to
        // 8000: still tractable per-call (~ms-scale with the augmented
        // Gauss + memoization), and unlocks more Stroeder cases.
        //   override:  XOLVER_NIA_FARKAS_OR_MAX_B
        std::size_t maxB = static_cast<std::size_t>(
            env::paramLong("XOLVER_NIA_FARKAS_OR_MAX_B", 8000));
        cachedTable = solverBuild.buildTable(cachedProfile, maxB);
        cachedIr = coreIr_;
    }
    if (!cachedProfile.good()) return std::nullopt;
    const auto& profile = cachedProfile;
    const auto& table = cachedTable;
    farkas::FarkasOrSolver solver(*coreIr_);
    static const bool trace = std::getenv("XOLVER_NIA_FARKAS_OR_TRACE");
    auto traceWrite = [&](const std::string& s) {
        if (!trace) return;
        FILE* f = std::fopen("/tmp/farkas_or_trace", "a");
        if (f) { std::fputs(s.c_str(), f); std::fputc('\n', f); std::fclose(f); }
    };
    traceWrite("stageFarkasOr: profile.blocks=" + std::to_string(profile.blocks.size())
               + " feasibleTotal=" + std::to_string(table.feasibleTotal)
               + " rows=" + std::to_string(table.rows.size()));
    // Outer-assertion structure dump (XOLVER_NIA_FARKAS_OUTER_DIAG).
    // For each outer assertion, prints kind + variable name + whether it
    // structurally looks like `(= var const)` (a hard equality forcing the
    // var). Used to design row-refute-by-outer-eq sound UNSAT path.
    if (std::getenv("XOLVER_NIA_FARKAS_OUTER_DIAG")) {
        // Helper: recursively check if `e` is a `(= var const)` form (either
        // child a Variable, the other an evaluable integer constant) and
        // return (varName, constValue) if so.
        std::function<bool(ExprId, std::string&, mpz_class&)> matchEqVarConst;
        matchEqVarConst = [&](ExprId eid, std::string& outVar, mpz_class& outVal) -> bool {
            const auto& e = coreIr_->get(eid);
            if (e.kind == Kind::Eq && e.children.size() == 2) {
                for (int side = 0; side < 2; ++side) {
                    const auto& v = coreIr_->get(e.children[side]);
                    const auto& c = coreIr_->get(e.children[1 - side]);
                    if (v.kind == Kind::Variable) {
                        auto* nm = std::get_if<std::string>(&v.payload.value);
                        if (!nm) continue;
                        if (c.kind == Kind::ConstInt) {
                            if (auto* iv = std::get_if<int64_t>(&c.payload.value)) {
                                outVar = *nm; outVal = *iv; return true;
                            }
                            if (auto* sv = std::get_if<std::string>(&c.payload.value)) {
                                try { outVal = mpz_class(*sv); outVar = *nm; return true; } catch (...) {}
                            }
                        }
                    }
                }
            }
            return false;
        };
        std::fprintf(stderr, "[FARKAS_OUTER_DIAG] outer count=%zu\n",
                     profile.outerAssertions.size());
        for (std::size_t i = 0; i < profile.outerAssertions.size(); ++i) {
            ExprId aid = profile.outerAssertions[i];
            const auto& e = coreIr_->get(aid);
            std::fprintf(stderr, "  outer[%zu] id=%u kind=%d", i, aid, static_cast<int>(e.kind));
            // If it's an And, scan its conjuncts for (= var const) patterns.
            if (e.kind == Kind::And) {
                std::fprintf(stderr, " conjuncts=%zu", e.children.size());
                for (ExprId c : e.children) {
                    std::string vn; mpz_class vv;
                    if (matchEqVarConst(c, vn, vv)) {
                        std::fprintf(stderr, " FORCES[%s=%s]",
                                     vn.c_str(), vv.get_str().c_str());
                    }
                }
            } else {
                std::string vn; mpz_class vv;
                if (matchEqVarConst(aid, vn, vv)) {
                    std::fprintf(stderr, " FORCES[%s=%s]",
                                 vn.c_str(), vv.get_str().c_str());
                }
            }
            std::fprintf(stderr, "\n");
        }
    }
    if (trace) {
        for (std::size_t i = 0; i < profile.blocks.size(); ++i) {
            const auto& blk = profile.blocks[i];
            std::string line = "  block[" + std::to_string(i) + "] branches="
                + std::to_string(blk.branches.size());
            traceWrite(line);
            for (std::size_t j = 0; j < blk.branches.size(); ++j) {
                const auto& br = blk.branches[j];
                std::string bl = "    branch[" + std::to_string(j) + "] λ=";
                for (const auto& l : br.lambdas) bl += l + ",";
                bl += " eqs=" + std::to_string(br.equalities.size())
                    + " ineqs=" + std::to_string(br.inequalities.size())
                    + " unclass=" + std::to_string(br.unclassified.size());
                if (j < blk.branchProxies.size() && !blk.branchProxies[j].empty()) {
                    bl += " proxy=" + blk.branchProxies[j];
                }
                traceWrite(bl);
            }
        }
    }
    if (trace) {
        for (std::size_t i = 0; i < table.rows.size(); ++i) {
            const auto& r = table.rows[i];
            std::string line = "  row[" + std::to_string(i) + "] (block=" +
                std::to_string(r.blockIdx) + " branch=" + std::to_string(r.branchIdx) + ") B={";
            bool first = true;
            for (const auto& [v, val] : r.bTuple) {
                if (!first) line += ", ";
                first = false;
                line += v + "=" + val.get_str();
            }
            line += "} ray=[";
            for (std::size_t j = 0; j < r.candidate.lambdaRay.size(); ++j) {
                if (j) line += ",";
                line += r.candidate.lambdaRay[j].get_str();
            }
            line += "]";
            traceWrite(line);
        }
    }
    // Bounded-B real-relaxation refutation runs INDEPENDENTLY of the support
    // table (it enumerates the bounded-B domain itself), so try it before the
    // empty-table / CSP paths — for cases like Stroeder loop3 the table is empty
    // (no single-ray Farkas certificate) yet the bounded-B per-leaf refutation
    // can still prove integer UNSAT. Default-OFF; soundness self-checked inside.
    if (auto refute = tryBoundedBRefutation(profile)) return refute;
    if (table.rows.empty()) {
        traceWrite("  exhaustive=" + std::string(table.exhaustive ? "true" : "false")
                   + " outerAssertions=" + std::to_string(profile.outerAssertions.size()));
        bool unsafeNoOuterCheck = std::getenv("XOLVER_NIA_FARKAS_OR_UNSAT_EMIT_UNSAFE") != nullptr;
        if (table.exhaustive && (unsafeNoOuterCheck || profile.outerAssertions.empty()) &&
            std::getenv("XOLVER_NIA_FARKAS_OR_UNSAT_EMIT")) {
            traceWrite("  → exhaustive empty table + no outer assertions => UNSAT");
            // iter-49: build a NARROW conflict from only Farkas-block
            // proxy literals (boolpur_K). For each block: pick the
            // currently-true branch proxy, add its negation. This says
            // "the current branch-choice combo is bad"; SAT backtracks
            // through ONLY proxy decisions (~10 vars), not the full
            // trail (~100s of vars). Falls back to full trail on miss.
            // CRITICAL: TheoryConflict.clause stores RAW reason literals
            // that are TRUE on the trail. TheoryManager negates them when
            // submitting the clause as a falsified external conflict. So
            // we push a.reason AS-IS (not .negated()) -- pushing .negated()
            // double-negates and produces an unsound conflict.
            TheoryConflict tc;
            if (registry_) {
                std::unordered_set<SatVar> seen;
                auto pushReason = [&](SatVar sv) {
                    if (!seen.insert(sv).second) return;
                    for (const auto& a : active_) {
                        if (a.reason.var == sv) {
                            tc.clause.push_back(a.reason);  // RAW reason
                            return;
                        }
                    }
                };
                for (const auto& blk : profile.blocks) {
                    // (a) Tseitin-proxy branches (iter-49 path).
                    for (const auto& proxy : blk.branchProxies) {
                        if (proxy.empty()) continue;
                        if (auto sv = registry_->findBoolVariableSatVar(proxy)) pushReason(*sv);
                    }
                    // (b) Unproxied branches: resolve the originalAnd ExprId.
                    for (const auto& br : blk.branches) {
                        if (br.originalAnd == NullExpr) continue;
                        if (auto sv = registry_->findSatVarByExprId(br.originalAnd))
                            pushReason(*sv);
                    }
                }
            }
            if (tc.clause.empty()) {
                tc.clause.reserve(active_.size());
                for (const auto& a : active_) tc.clause.push_back(a.reason);  // RAW
            }
            std::cerr << "[FarkasOrUnsatEmit] exhaustive empty table; emit conflict size=" << tc.clause.size() << "\n";
            return TheoryCheckResult::mkConflict(std::move(tc));
        }
        traceWrite("  → empty table; bail");
        return std::nullopt;
    }

    // Enumerate up to N candidate CSP assignments; iterate validator.
    auto assignments = solver.enumerateCsp(table, profile, /*maxResults=*/64);
    if (assignments.empty()) {
        traceWrite("  → no CSP assignments; bail");
        return std::nullopt;
    }
    traceWrite("  → CSP enumerated " + std::to_string(assignments.size()) + " candidates");
    farkas::FarkasOrModelAssembler assembler(*coreIr_);

    // Residual repair helper: a Farkas-Or candidate fixes the Farkas-bound
    // λ-rays, B-tuple and CT-vars, but the original formula often contains
    // RESIDUAL vars (e.g. main_x, main_y in Stroeder) that appear in outer
    // assertions like `(<= (+ Nl2CT (* Nl2main_x main_x) ...) 0)`. The
    // assembler defaults residuals to 0, which forces the bilinear term to
    // 0 and the assertion to `c0 ≤ 0` — guaranteed to fail when Farkas
    // forced c0 ≥ 1. To recover, after a candidate's first validation fails
    // we try a small grid of residual values and re-validate. Grid width
    // adapts to residual count so the combo product stays bounded.
    static const std::size_t COMBO_CAP = static_cast<std::size_t>(
        env::paramLong("XOLVER_NIA_FARKAS_COMBO_CAP", 16384));
    auto gridFor = [](std::size_t n) -> std::vector<mpz_class> {
        std::vector<mpz_class> v;
        if (n == 0) return v;
        if (n <= 3) {
            for (long k : {0L, 1L, -1L, 2L, -2L, 10L, -10L, 100L, -100L})
                v.emplace_back(k);
        } else if (n <= 5) {
            for (long k : {0L, 1L, -1L, 2L, -2L}) v.emplace_back(k);
        } else if (n <= 8) {
            for (long k : {0L, 1L, -1L}) v.emplace_back(k);
        } // n > 8: empty → caller skips repair
        return v;
    };

    // Per-stage-call validation budget: residual repair can otherwise dwarf
    // the rest of the NIA pipeline. We cap total validator invocations per
    // stage call. The stage runs many times during a check loop, so this
    // is a per-call (not per-check) budget.
    static const std::size_t VALIDATE_BUDGET = static_cast<std::size_t>(
        env::paramLong("XOLVER_NIA_FARKAS_VALIDATE_BUDGET", 200));
    std::size_t validations = 0;
    // Pre-compute var name → isBool map by walking all assertions once.
    // Bool vars (e.g. boolpur_K Tseitin proxies) MUST go through
    // BoolAssignment; if routed through NumAssignment the validator hits
    // `(= boolpur_K (and ...))` with Number(0) LHS vs Bool RHS and
    // returns Indeterminate — which the framework treats as failure.
    std::unordered_set<std::string> boolVarNames;
    {
        SortId boolSort = coreIr_->boolSortId();
        std::function<void(ExprId)> walkSort;
        std::unordered_set<ExprId> seen;
        walkSort = [&](ExprId id) {
            if (!seen.insert(id).second) return;
            const auto& e = coreIr_->get(id);
            if (e.kind == Kind::Variable && e.sort == boolSort) {
                if (auto* s = std::get_if<std::string>(&e.payload.value))
                    boolVarNames.insert(*s);
            }
            for (ExprId c : e.children) walkSort(c);
        };
        for (ExprId aid : coreIr_->assertions()) walkSort(aid);
    }

    auto tryValidate = [&](IntegerModel& M) -> bool {
        if (validations >= VALIDATE_BUDGET) return false;
        ++validations;
        ArithModelValidator::NumAssignment num;
        ArithModelValidator::BoolAssignment bools;
        num.reserve(M.size());
        for (const auto& [v, val] : M) {
            if (boolVarNames.count(v)) {
                bools.emplace(v, val != 0);
            } else {
                num.emplace(v, mpq_class(val));
            }
        }
        ArithModelValidator amv(*coreIr_, num, bools);
        auto verdict = amv.validate(coreIr_->assertions());
        // Per-assertion failure diag: walk each assertion individually,
        // report which fail. Gated on XOLVER_NIA_FARKAS_FAILDIAG so the
        // default path is identical.
        if (verdict != ArithModelValidator::Verdict::Satisfied &&
            std::getenv("XOLVER_NIA_FARKAS_FAILDIAG")) {
            for (std::size_t ai = 0; ai < coreIr_->assertions().size(); ++ai) {
                ExprId aid = coreIr_->assertions()[ai];
                auto v = amv.validate({aid});
                if (v != ArithModelValidator::Verdict::Satisfied) {
                    std::fprintf(stderr, "    [FAILDIAG] assertion[%zu] (id=%u) verdict=%d\n",
                                 ai, aid, static_cast<int>(v));
                }
            }
        }
        return verdict == ArithModelValidator::Verdict::Satisfied;
    };

    int candIdx = 0;
    for (const auto& assignment : assignments) {
        auto candidate = assembler.assemble(profile, assignment);
        if (!candidate) { ++candIdx; continue; }
        if (trace) {
            std::string line = "  cand[" + std::to_string(candIdx) + "]:";
            for (const auto& [v, val] : *candidate) {
                line += " " + v + "=" + val.get_str();
            }
            traceWrite(line);
        }
        if (tryValidate(*candidate)) {
            traceWrite("  → validator SAT (cand[" + std::to_string(candIdx) + "])");
            currentModel_ = *candidate;
            lastValidatedFarkasModel_ = std::move(*candidate);   // survives reset

            // Queue unit-lemma propagations for the chosen branches'
            // boolpur_K Tseitin proxies. Each unit lemma drives the
            // SAT-CDCL engine onto a trail consistent with the Farkas-Or
            // model so it actually returns Sat instead of looping in the
            // decision search. They are drained by stagePendingLemma the
            // next time the propagator polls, which routes through the
            // proper lemma-database channel (CaDiCaL refuses raw
            // addClause mid-solve, so we cannot use pinLiteral here).
            //
            // Sound: the model was validator-confirmed against the
            // original CoreIr, so pinning the matching boolpur values
            // only prunes explorations that contradict a positively
            // confirmed witness. Each (proxy, truth) pair is queued at
            // most once via pinnedProxies_ — these unit clauses are
            // permanent in the SAT backend; duplicates are noise.
            std::vector<TheoryLemma> newPinLemmas;
            if (registry_) {
                for (std::size_t j = 0; j < profile.blocks.size(); ++j) {
                    const auto& blk = profile.blocks[j];
                    auto cit = assignment.choice.find((int)j);
                    int chosen = (cit != assignment.choice.end()) ? cit->second : -1;
                    for (std::size_t k = 0; k < blk.branchProxies.size(); ++k) {
                        const auto& proxy = blk.branchProxies[k];
                        if (proxy.empty()) continue;
                        bool truth = ((int)k == chosen);
                        auto pinKey = proxy + (truth ? ":1" : ":0");
                        if (!pinnedProxies_.insert(pinKey).second) continue;
                        auto sv = registry_->findBoolVariableSatVar(proxy);
                        if (!sv) continue;
                        TheoryLemma ulemma;
                        ulemma.lits.push_back(truth ? SatLit::positive(*sv)
                                                     : SatLit::negative(*sv));
                        ulemma.kind = LemmaKind::Entailment;
                        if (!lemmaDb.contains(ulemma)) {
                            lemmaDb.insertIfNew(ulemma);
                            newPinLemmas.push_back(ulemma);
                            traceWrite("  → queue pin-lemma " + proxy + "=" +
                                       (truth ? "true" : "false"));
                        }
                    }
                }
            }

            // Emit pin-lemmas via the proper SAT-CDCL lemma channel. The
            // first lemma is returned directly via mkLemma so it's installed
            // immediately; the rest (if any) queue into pendingLinLemmas_
            // and drain via stagePendingLemma on subsequent check() calls.
            // Returning consistent() instead would short-circuit the
            // pipeline and the lemmas would never reach SAT.
            if (!newPinLemmas.empty()) {
                auto first = std::move(newPinLemmas.front());
                for (std::size_t i = 1; i < newPinLemmas.size(); ++i) {
                    pendingLinLemmas_.push_back(std::move(newPinLemmas[i]));
                }
                return TheoryCheckResult::mkLemma(first);
            }
            // No new pin-lemmas to queue: every proxy that needed
            // committing has already been committed. The framework has
            // confirmed this validated SAT model farkasOrSatStreak_
            // times in a row; if SAT-CDCL still hasn't converged on its
            // own, return Unknown so cb_propagate / cb_check_found_model
            // both terminate SAT and the Cap. 10 hook in Solver.cpp
            // promotes the theory candidate directly via
            // modelPositivelyValidates. SOUND: same Unknown-recovery
            // contract — validator must positively confirm the model
            // before Sat is emitted.
            constexpr int kFarkasOrSatStreakLimit = 3;
            if (++farkasOrSatStreak_ >= kFarkasOrSatStreakLimit) {
                farkasOrSatStreak_ = 0;
                return TheoryCheckResult::unknown(
                    "NIA Farkas-Or: validated model, SAT-CDCL did not converge");
            }
            return TheoryCheckResult::consistent();
        }

        // First-pass failed. Identify residual vars: those assigned to 0
        // by the default residual pass AND not present in any Farkas
        // assignment (B, λ, CT, or ANY branch's λ in the detected blocks
        // — unused-branch λ's are validly 0 since only one Or branch per
        // block needs to hold; perturbing them is wasted search).
        std::vector<std::string> residualVars;
        std::unordered_set<std::string> fixed;
        for (const auto& [v, _] : assignment.B) fixed.insert(v);
        for (const auto& [_, names] : assignment.lambdaNamesPerBlock)
            for (const auto& n : names) fixed.insert(n);
        for (const auto& [v, _] : assignment.ctInterval) fixed.insert(v);
        // Also pin ALL Or-branch λ's (chosen or not) — perturbing an
        // unchosen branch's λ won't satisfy the Or unless that branch's
        // full Farkas template is also satisfied, which we don't try.
        for (const auto& blk : profile.blocks) {
            for (const auto& br : blk.branches) {
                for (const auto& n : br.lambdas) fixed.insert(n);
            }
        }
        for (const auto& [v, val] : *candidate) {
            if (fixed.count(v)) continue;
            // Only sweep over vars defaulted to 0 (the residual repair target).
            if (val != 0) continue;
            residualVars.push_back(v);
        }
        auto values = gridFor(residualVars.size());
        if (values.empty()) {
            ++candIdx;
            continue;
        }
        if (trace) {
            std::string line = "  cand[" + std::to_string(candIdx) + "] residual-repair over "
                + std::to_string(residualVars.size()) + " vars, grid=" + std::to_string(values.size())
                + ", combos=" + std::to_string(values.size());
            traceWrite(line);
        }

        // Geometric grid enumeration with combo cap.
        std::size_t total = 1;
        for (std::size_t i = 0; i < residualVars.size(); ++i) {
            total *= values.size();
            if (total > COMBO_CAP) { total = 0; break; }
        }
        if (total == 0) { ++candIdx; continue; }

        std::vector<std::size_t> idx(residualVars.size(), 0);
        while (true) {
            if (validations >= VALIDATE_BUDGET) break;
            // Skip the all-zero combo (already tried).
            bool allZero = true;
            for (std::size_t i = 0; i < idx.size(); ++i) {
                if (values[idx[i]] != 0) { allZero = false; break; }
            }
            if (!allZero) {
                IntegerModel repaired_M = *candidate;
                for (std::size_t i = 0; i < residualVars.size(); ++i) {
                    repaired_M[residualVars[i]] = values[idx[i]];
                }
                if (tryValidate(repaired_M)) {
                    traceWrite("  → validator SAT after residual-repair (cand["
                               + std::to_string(candIdx) + "])");
                    currentModel_ = std::move(repaired_M);
                    return TheoryCheckResult::consistent();
                }
            }
            // Increment odometer-style.
            std::size_t pos = 0;
            while (pos < idx.size()) {
                ++idx[pos];
                if (idx[pos] < values.size()) break;
                idx[pos] = 0;
                ++pos;
            }
            if (pos == idx.size()) break;
        }
        if (validations >= VALIDATE_BUDGET) break;
        ++candIdx;
    }
    traceWrite("  → no candidate validated");
    // (bounded-B refutation already attempted before the CSP path above.)
    return std::nullopt;
}

std::optional<TheoryCheckResult>
NiaSolver::tryBoundedBRefutation(const farkas::FarkasProfile& profile) {
    // PROMOTED default-ON (2026-06-08) — see stageFarkasOr. Returns nullopt
    // immediately unless the formula is Farkas-Or-shaped with bounded template
    // coeffs, so the cost on every other NIA solve is two empty-container checks.
#ifndef XOLVER_HAS_LIBPOLY
    return std::nullopt;  // needs the libpoly algebra backend (CdcacCore)
#else
    if (!kernel_ || !coreIr_ || !converter_) return std::nullopt;
    if (profile.boundedGlobals.empty() || profile.blocks.empty())
        return std::nullopt;

    // Once-per-solve cache: the refutation verdict depends only on the formula
    // (coreIr_), not the trail, so a not-refutable outcome is memoized to avoid
    // re-running the expensive per-leaf CdcacCore enumeration on every Full-effort
    // cb_propagate. (An UNSAT outcome ends the solve, so it is never reached
    // again — no need to cache it.)
    static thread_local const CoreIr* refuteNotRefutableIr = nullptr;
    if (refuteNotRefutableIr == coreIr_) return std::nullopt;
    auto giveUp = [&]() -> std::optional<TheoryCheckResult> {
        refuteNotRefutableIr = coreIr_;
        return std::nullopt;
    };

    static const bool trace = std::getenv("XOLVER_NIA_FARKAS_OR_TRACE");
    auto traceWrite = [&](const std::string& s) {
        if (!trace) return;
        FILE* f = std::fopen("/tmp/farkas_or_trace", "a");
        if (f) { std::fputs(s.c_str(), f); std::fputc('\n', f); std::fclose(f); }
    };
    traceWrite("[bounded-refute] FUNCTION ENTERED blocks=" + std::to_string(profile.blocks.size())
               + " bounded=" + std::to_string(profile.boundedGlobals.size())
               + " dnf=" + std::to_string(profile.dnfBlocks.size()));

    // ---- 1. Bounded-B domain: collect vars + integer intervals, cap product.
    struct BVar { VarId vid; mpz_class lo, hi; };
    std::vector<BVar> bvars;
    bvars.reserve(profile.boundedGlobals.size());
    const long domCap = env::paramLong("XOLVER_NIA_FARKAS_REFUTE_DOM_CAP", 8192);
    mpz_class domProduct = 1;
    for (const auto& [name, bound] : profile.boundedGlobals) {
        mpz_class span = bound.second - bound.first + 1;
        if (span <= 0) return std::nullopt;          // empty/degenerate domain
        domProduct *= span;
        if (domProduct > domCap) {
            traceWrite("  [bounded-refute] B-domain " + domProduct.get_str()
                       + " > cap " + std::to_string(domCap) + "; bail");
            return std::nullopt;                       // too large; bail (sound)
        }
        bvars.push_back({kernel_->getOrCreateVar(name), bound.first, bound.second});
    }

    // ---- 2. Validity only: every block must offer at least one branch.
    // The old hard `comboCount > 256` ceiling is GONE — it was an artificial
    // floor that bailed (→ unknown) on every Farkas-Or UNSAT with > 8 binary
    // blocks (Hanoi 12 blocks = 4096 combos, etc.), which a uniform VeryMax
    // sweep showed to be the single largest miss class. The flat odometer it
    // guarded is replaced below by a DFS with sound prefix-UNSAT pruning, so
    // the branch-combo product no longer needs a ceiling: genuinely-UNSAT
    // termination problems collapse at a shallow prefix.
    for (const auto& blk : profile.blocks)
        if (blk.branches.empty()) return std::nullopt;
    traceWrite("  [bounded-refute] B-domain=" + domProduct.get_str()
               + " outer=" + std::to_string(profile.outerAssertions.size()));

    if (!cdcacCore_) {
        cdcacAlgebra_ = std::make_unique<LibpolyBackend>(kernel_.get());
        cdcacCore_ = std::make_unique<CdcacCore>(kernel_.get(), cdcacAlgebra_.get());
    }

    // relHolds: does the rational constant `c` satisfy `c rel 0`?
    auto relHolds = [](const mpq_class& c, Relation rel) -> bool {
        switch (rel) {
            case Relation::Eq:  return c == 0;
            case Relation::Neq: return c != 0;
            case Relation::Lt:  return c <  0;
            case Relation::Leq: return c <= 0;
            case Relation::Gt:  return c >  0;
            case Relation::Geq: return c >= 0;
        }
        return false;
    };

    // Convert a relational atom ExprId into a (poly, rel) constraint with B
    // substituted. Outcomes:
    //   kAdd        -> append `out` to the leaf system
    //   kTrue       -> trivially satisfied (skip)
    //   kFalse      -> trivially violated  -> leaf is infeasible
    //   kBail       -> not modellable      -> whole refutation must bail (sound)
    enum class AtomOutcome { kAdd, kTrue, kFalse, kBail };
    auto atomToConstraint =
        [&](ExprId atomId, const std::unordered_map<VarId, mpz_class>& Bvals,
            CdcacConstraint& out) -> AtomOutcome {
        const auto& e = coreIr_->get(atomId);
        Relation rel;
        switch (e.kind) {
            case Kind::Gt:  rel = Relation::Gt;  break;
            case Kind::Geq: rel = Relation::Geq; break;
            case Kind::Lt:  rel = Relation::Lt;  break;
            case Kind::Leq: rel = Relation::Leq; break;
            case Kind::Eq:  rel = Relation::Eq;  break;
            default: return AtomOutcome::kBail;   // Neq / non-relational atom
        }
        if (e.children.size() != 2) return AtomOutcome::kBail;
        auto cc = converter_->convertConstraint(e.children[0], e.children[1],
                                                rel, *coreIr_);
        if (cc.status == PolyConstraintStatus::Tautology) return AtomOutcome::kTrue;
        if (cc.status == PolyConstraintStatus::Conflict)  return AtomOutcome::kFalse;
        if (cc.status != PolyConstraintStatus::Constraint) return AtomOutcome::kBail;
        PolyId diff = cc.diff;
        // INTEGER TIGHTENING (the lever that makes the real relaxation decisive).
        // Every variable is integer and every coefficient integer, so `diff` is
        // integer-valued on any integer assignment. Hence over ℤ:
        //     diff >  0  ⟺  diff − 1 ≥ 0
        //     diff <  0  ⟺  diff + 1 ≤ 0
        // Replacing the strict atom with its tightened non-strict form keeps the
        // integer solution set unchanged while SHRINKING the real-relaxation
        // feasible region (S_int ⊆ S'_real). Without this a strict ineq like
        // `CT·λ > 1` with `CT < 1` is real-feasible via fractional CT even though
        // it is integer-infeasible — exactly the Stroeder/VeryMax shape.
        if (rel == Relation::Gt) {
            diff = kernel_->sub(diff, kernel_->mkOne());
            rel = Relation::Geq;
        } else if (rel == Relation::Lt) {
            diff = kernel_->add(diff, kernel_->mkOne());
            rel = Relation::Leq;
        }
        for (const auto& [vid, val] : Bvals) {
            if (auto sp = kernel_->substituteRational(diff, vid, mpq_class(val)))
                diff = *sp;
        }
        if (kernel_->isConstant(diff))
            return relHolds(kernel_->toConstant(diff), rel)
                       ? AtomOutcome::kTrue : AtomOutcome::kFalse;
        out.poly = diff;
        out.rel = rel;
        out.reason = SatLit{0, true};   // placeholder; conflict built separately
        return AtomOutcome::kAdd;
    };

    // Flatten an outer assertion (possibly nested And) into leaf constraints.
    // Returns AtomOutcome semantics over the whole subtree: kFalse if any atom
    // is trivially violated, kBail if any atom is unmodellable / contains an Or.
    std::function<AtomOutcome(ExprId, const std::unordered_map<VarId, mpz_class>&,
                              std::vector<CdcacConstraint>&)> flatten;
    flatten = [&](ExprId eid, const std::unordered_map<VarId, mpz_class>& Bvals,
                  std::vector<CdcacConstraint>& cons) -> AtomOutcome {
        const auto& e = coreIr_->get(eid);
        if (e.kind == Kind::And) {
            for (ExprId c : e.children) {
                AtomOutcome o = flatten(c, Bvals, cons);
                if (o == AtomOutcome::kFalse || o == AtomOutcome::kBail) return o;
            }
            return AtomOutcome::kAdd;
        }
        if (e.kind == Kind::Or || e.kind == Kind::Not)
            return AtomOutcome::kBail;   // disjunction / negation in outer: bail
        CdcacConstraint c;
        AtomOutcome o = atomToConstraint(eid, Bvals, c);
        if (o == AtomOutcome::kAdd) cons.push_back(std::move(c));
        return o;
    };

    // Cost/slack vars to eliminate existentially in the LIA leaf engine
    // (research note 2026-06-07: ∃CT. A+CT·S ⋈ 0 ≡ S≠0 ∨ A⋈0). PROMOTED
    // default-ON (2026-06-08): the CT-elim leaf path is the one that actually
    // discharges the +11 VeryMax UNSAT (the CdcacCore fallback below stays as a
    // safety net for shapes the over-approx parse can't model).
    const bool ctElim = true;
    std::unordered_set<VarId> ctVarSet;
    if (ctElim)
        for (const auto& nm : profile.unboundedCT)
            ctVarSet.insert(kernel_->getOrCreateVar(nm));

    // ---- 3. Enumerate B-tuples × branch combos; each leaf must be Unsat.
    // The refutation odometer enumerates the flat Farkas-Or blocks AND any
    // DNF-recovered nested Or blocks (XOLVER_NIA_FARKAS_DNF_BLOCKS) uniformly:
    // both demand "pick one branch, every combo must be UNSAT". DNF blocks are
    // kept out of profile.blocks (their empty branchProxies must not reach the
    // SAT model-assembler) but are exactly the constraints whose omission made
    // the leaf incomplete, so the refutation MUST include them.
    std::vector<const farkas::FarkasOrBlock*> allBlocks;
    allBlocks.reserve(profile.blocks.size() + profile.dnfBlocks.size());
    for (const auto& b : profile.blocks)    allBlocks.push_back(&b);
    for (const auto& b : profile.dnfBlocks) allBlocks.push_back(&b);
    traceWrite("[bounded-refute] enter flat=" + std::to_string(profile.blocks.size())
               + " dnf=" + std::to_string(profile.dnfBlocks.size())
               + " residual=" + std::to_string(profile.residualConstraints.size()));

    std::vector<mpz_class> bcur;
    for (const auto& bv : bvars) bcur.push_back(bv.lo);
    std::size_t leavesChecked = 0;
    std::size_t prefixChecks = 0;
    // Safety backstop ONLY (not a perf floor): the DFS prunes genuinely-UNSAT
    // trees fast and bails to giveUp() the moment a real-feasible leaf is hit,
    // so this trips only on a pathological tree that neither prunes nor finds a
    // feasible leaf. On trip we giveUp() → Unknown (sound), never a wrong UNSAT.
    // Set high; lower via XOLVER_NIA_FARKAS_REFUTE_LEAF_CAP if a case runs long.
    const std::size_t leafCap = static_cast<std::size_t>(
        env::paramLong("XOLVER_NIA_FARKAS_REFUTE_LEAF_CAP", 200000));
    while (true) {
        std::unordered_map<VarId, mpz_class> Bvals;
        for (std::size_t i = 0; i < bvars.size(); ++i) Bvals[bvars[i].vid] = bcur[i];

        // Mandatory residual (proxy-resolved) constraints for this B, shared
        // across branch combos. Use profile.residualConstraints (clean atoms),
        // NOT the raw purified outerAssertions. An unmodellable atom (kBail) is
        // SKIPPED, not aborted: dropping a constraint only ENLARGES the feasible
        // set, so a per-leaf UNSAT over the smaller constraint set is still a
        // sound UNSAT of the original.
        std::vector<CdcacConstraint> outerCons;
        bool bTupleDead = false;     // some outer atom trivially violated ⇒ all
                                     // branch combos at this B are infeasible
        for (ExprId rc : profile.residualConstraints) {
            AtomOutcome oo = flatten(rc, Bvals, outerCons);
            if (oo == AtomOutcome::kFalse) { bTupleDead = true; break; }
            // kAdd appended already; kTrue/kBail → skip
        }

        if (!bTupleDead) {
            // Branch-combo SEARCH: DFS over blocks with sound prefix-UNSAT
            // pruning (replaces the old flat odometer). The leaf constraint set
            // grows monotonically with each chosen branch and the CT-elim
            // over-approx UNSAT test is monotone, so a prefix whose PARTIAL leaf
            // is already UNSAT refutes EVERY completion of that prefix — prune
            // the whole subtree (sound: pruning never drops a feasible leaf, so
            // it can never cause a wrong UNSAT). Genuinely-UNSAT termination
            // problems go UNSAT at a shallow prefix, collapsing the 2^blocks
            // tree; only a real-feasible/unknown FULL leaf forces giveUp.
            //   returns 0 = subtree fully refuted (all completions UNSAT)
            //           1 = giveUp (feasible/unknown full leaf, unmodellable
            //               atom, or safety backstop tripped)
            std::function<int(std::size_t, const std::vector<CdcacConstraint>&)> dfs;
            dfs = [&](std::size_t bi,
                      const std::vector<CdcacConstraint>& accum) -> int {
                if (leavesChecked + prefixChecks > leafCap) {
                    traceWrite("  [bounded-refute] leaf/prefix budget "
                               + std::to_string(leafCap) + " tripped; giveUp");
                    return 1;
                }
                if (bi == allBlocks.size()) {
                    // FULL leaf — exact check. Over-approx (∃CT. A+CT·S ⋈ 0 ≡
                    // S≠0 ∨ A⋈0) first; else the real-relaxation CdcacCore. A
                    // feasible/unknown full leaf ⇒ NOT refutable ⇒ giveUp.
                    if (ctElim && niaLeafFarkasLiaUnsat(accum, ctVarSet, *kernel_)) {
                        ++leavesChecked; return 0;
                    }
                    CdcacInput input;
                    input.constraints = accum;
                    // varOrder = sorted union of leaf-constraint vars (CdcacCore
                    // indexes it directly; empty ⇒ n=0 ⇒ immediate Unknown).
                    // integerVars stays empty → PURE REAL relaxation (sound for
                    // UNSAT; integrality is injected via strict-ineq tightening
                    // in atomToConstraint).
                    std::set<VarId> vset;
                    for (const auto& cc2 : input.constraints)
                        for (const std::string& vn : kernel_->variables(cc2.poly))
                            vset.insert(kernel_->getOrCreateVar(vn));
                    input.varOrder.assign(vset.begin(), vset.end());
                    // CRASH GUARD: the CdcacCore fallback runs a Lazard/CAD
                    // projection whose libpoly subresultant (psc) chain blows up
                    // coefficient sizes super-exponentially with the number of
                    // projection levels (= variable count). On a high-dimensional
                    // leaf (consts5nt) it exhausts RAM and SIGSEGVs inside
                    // coefficient_ensure_capacity — a hardware fault that cannot be
                    // caught. Prevent it: skip the fallback above a variable budget,
                    // forfeiting only THIS leaf (giveUp → Unknown). Sound — the
                    // refutation merely fails to prove this leaf UNSAT, never emits a
                    // wrong UNSAT. The over-approx above already decides the
                    // tractable leaves, so a leaf reaching here that is also
                    // high-dimensional is one CdcacCore could not finish anyway.
                    traceWrite("  [bounded-refute] cdcac-fallback leaf vars="
                               + std::to_string(input.varOrder.size()));
                    // Threshold 24: above the largest CdcacCore leaf the
                    // refutation-solvable cases actually need (measured: Ex04 = 9,
                    // 4Nested = 19, both decidable, no crash) yet below the
                    // dimension whose libpoly subresultant chain OOMs/SIGSEGVs
                    // (consts5nt = 44). Biased toward the solvable max + margin
                    // because a crash is catastrophic (lost batch) while a forfeited
                    // leaf is benign (Unknown, not wrong). Tunable for experiments.
                    static const size_t kMaxLeafVars = static_cast<size_t>(
                        env::paramLong("XOLVER_NIA_FARKAS_REFUTE_MAX_LEAF_VARS", 24));
                    if (kMaxLeafVars > 0 && input.varOrder.size() > kMaxLeafVars) {
                        traceWrite("  [bounded-refute] leaf vars > " + std::to_string(kMaxLeafVars)
                                   + "; skip CdcacCore fallback (giveUp, projection OOM-risk)");
                        return 1;
                    }
                    ++leavesChecked;
                    CdcacResult cd = cdcacCore_->solve(input);
                    if (cd.status != CdcacStatus::Unsat) {
                        traceWrite("  [bounded-refute] leaf feasible/unknown "
                                   "(status=" + std::to_string((int)cd.status)
                                   + "); bail");
                        return 1;
                    }
                    return 0;
                }
                const auto* blk = allBlocks[bi];
                for (std::size_t b = 0; b < blk->branches.size(); ++b) {
                    const auto& br = blk->branches[b];
                    std::vector<CdcacConstraint> cons = accum;
                    bool leafDead = false, leafBail = false;
                    for (const auto& lam : br.lambdas) {   // lambda >= 0
                        CdcacConstraint c;
                        c.poly = kernel_->mkVar(kernel_->getOrCreateVar(lam));
                        c.rel = Relation::Geq;
                        c.reason = SatLit{0, true};
                        cons.push_back(std::move(c));
                    }
                    auto addAtoms = [&](const std::vector<ExprId>& atoms) {
                        for (ExprId a : atoms) {
                            CdcacConstraint c;
                            AtomOutcome o = atomToConstraint(a, Bvals, c);
                            if (o == AtomOutcome::kAdd) cons.push_back(std::move(c));
                            else if (o == AtomOutcome::kFalse) { leafDead = true; return; }
                            else if (o == AtomOutcome::kBail)  { leafBail = true; return; }
                        }
                    };
                    addAtoms(br.equalities);
                    if (!leafDead && !leafBail) addAtoms(br.inequalities);
                    if (leafBail) {
                        traceWrite("[bounded-refute] leafBail block=" + std::to_string(bi)
                                   + " (atom unmodellable) ⇒ giveUp");
                        return 1;   // can't model a branch atom
                    }
                    if (leafDead) continue;   // branch trivially infeasible ⇒
                                              // its whole subtree is refuted
                    // PREFIX PRUNING: a sound over-approx UNSAT of this partial
                    // leaf refutes every completion ⇒ skip the subtree.
                    if (ctElim) {
                        ++prefixChecks;
                        if (niaLeafFarkasLiaUnsat(cons, ctVarSet, *kernel_)) continue;
                    }
                    if (dfs(bi + 1, cons) == 1) return 1;   // propagate giveUp
                }
                return 0;   // every branch at this level refuted
            };
            if (dfs(0, outerCons) == 1) return giveUp();
        }

        // advance B odometer (integer ranges [lo,hi])
        std::size_t p = 0;
        while (p < bvars.size()) {
            ++bcur[p];
            if (bcur[p] <= bvars[p].hi) break;
            bcur[p] = bvars[p].lo; ++p;
        }
        if (p == bvars.size()) break;
    }

    // Every (B-tuple, branch-combo) leaf is real-infeasible (or trivially dead).
    // ℤⁿ ⊆ ℝⁿ and the B domain was exhausted ⇒ sound integer UNSAT.
    traceWrite("  [bounded-refute] ALL " + std::to_string(leavesChecked)
               + " leaves real-infeasible ⇒ UNSAT");
    TheoryConflict tc;
    if (registry_) {
        std::unordered_set<SatVar> seen;
        auto pushReason = [&](SatVar sv) {
            if (!seen.insert(sv).second) return;
            for (const auto& a : active_) {
                if (a.reason.var == sv) { tc.clause.push_back(a.reason); return; }
            }
        };
        for (const auto* blk : allBlocks) {
            for (const auto& proxy : blk->branchProxies) {
                if (proxy.empty()) continue;
                if (auto sv = registry_->findBoolVariableSatVar(proxy)) pushReason(*sv);
            }
            for (const auto& br : blk->branches) {
                if (br.originalAnd == NullExpr) continue;
                if (auto sv = registry_->findSatVarByExprId(br.originalAnd))
                    pushReason(*sv);
            }
        }
    }
    if (tc.clause.empty()) {
        tc.clause.reserve(active_.size());
        for (const auto& a : active_) tc.clause.push_back(a.reason);
    }
    if (tc.clause.empty()) return std::nullopt;   // nothing to pin the conflict on
    std::cerr << "[FarkasOrBoundedRefute] all " << leavesChecked
              << " leaves real-infeasible; emit UNSAT conflict size="
              << tc.clause.size() << "\n";
    return TheoryCheckResult::mkConflict(std::move(tc));
#endif
}

// SAT14-attack: early-pipeline LS stage. Same LS instance, but invoked at
// the TOP of the pipeline (right after nia.normalize) instead of the end.
// The per-call and total budgets are explicitly clamped TIGHT here so the
// stage doesn't starve the upstream workhorses on inputs where LS is
// unlikely to help (e.g. UNSAT-heavy modular clusters where the modular
// reasoner is the right tool).
//
// SOUNDNESS: identical to stageLocalSearch — every Sat passes
// IntegerModelValidator on the ORIGINAL constraints. A failed early-LS
// just falls through to the rest of the pipeline.
std::optional<TheoryCheckResult> NiaSolver::stageLocalSearchEarly(TheoryLemmaStorage&, TheoryEffort) {
    static const bool earlyEnabled = [] {
        const char* e = std::getenv("XOLVER_NIA_LS_EARLY");
        return e && *e && *e != '0';
    }();
    if (!earlyEnabled) return std::nullopt;
    // Save the LS's current per-call / cumulative budgets. We TEMPORARILY
    // narrow them for this stage's run so the upstream workhorses still
    // get their share.
    static const long earlyBudgetMs =
        env::paramLong("XOLVER_NIA_LS_EARLY_BUDGET_MS", 200);
    static const long earlyTotalMs =
        env::paramLong("XOLVER_NIA_LS_EARLY_TOTAL_MS", 5000);
    // We DON'T mutate the LS's persistent state — only its budget setter.
    // The persistent NiaLsContext (warm-start state) is preserved across
    // calls, so each early-stage invocation continues the search from
    // where it left off.
    // NiaLocalSearch doesn't expose a getter for the per-call budget, so
    // we set it once and let the late-pipeline stage inherit the early
    // budget. That's the desired behavior on SAT14-attack runs: both
    // early + late LS share the same tight budget so the cumulative cap
    // doesn't accidentally run away. earlyTotalMs is read for forward-
    // compat once a cumulative-setter is wired up; currently informational.
    (void)earlyTotalMs;
    localSearch_.setBudgetMs(earlyBudgetMs);
    // HYB-X: pass partition hint to LS (cheap; partition is recomputed
    // here but the cost is bounded by normalized_.size()).
    {
        static const bool partHint = std::getenv("XOLVER_NIA_LS_PARTITION_HINT") != nullptr;
        if (partHint && !normalized_.empty()) {
            VariablePartition vp(*kernel_);
            auto pr = vp.partition(normalized_, domains_, 32);
            localSearch_.setPartitionHint(pr);
        }
    }
    if (auto model = localSearch_.tryFindModel(normalized_, domains_)) {
        if (validator_.validate(*model, normalized_) == IntegerModelValidator::Result::Valid) {
            currentModel_ = *model;
            return TheoryCheckResult::consistent();
        }
    }
    // No model found this call — the warm-start context retains progress
    // (when XOLVER_NIA_LS_WARM_START is on). Fall through to the rest of
    // the pipeline so the regular reasoners still get to run.
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stagePendingLemma(TheoryLemmaStorage&, TheoryEffort) {
    if (!pendingLinLemmas_.empty()) {
        auto lemma = std::move(pendingLinLemmas_.front());
        pendingLinLemmas_.pop_front();
        return TheoryCheckResult::mkLemma(lemma);
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageBranch(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    if (auto lemma = buildBranchLemma(normalized_, domains_, lemmaDb)) {
        return TheoryCheckResult::mkLemma(*lemma);
    }
    return TheoryCheckResult::unknown("NIA: no progress (finite domain not closed, branch lemma failed, local search failed)");
}

bool NiaSolver::relationSatisfied(const mpq_class& val, Relation rel) const {
    switch (rel) {
        case Relation::Eq:  return val == 0;
        case Relation::Neq: return val != 0;
        case Relation::Lt:  return val <  0;
        case Relation::Leq: return val <= 0;
        case Relation::Gt:  return val >  0;
        case Relation::Geq: return val >= 0;
    }
    return false;
}

std::optional<TheoryLemma> NiaSolver::buildBranchLemma(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const DomainStore& domains,
    TheoryLemmaStorage& lemmaDb) {

    if (!registry_) return std::nullopt;

    auto allVars = collectVars(constraints, *kernel_);
    if (allVars.empty()) return std::nullopt;

    // Collect candidate variables with their domain info
    struct Candidate {
        std::string var;
        bool hasLower;
        bool hasUpper;
        mpz_class lower;
        mpz_class upper;
        mpz_class rangeSize; // upper - lower, or 0 if unbounded
        int priority; // 0 = both bounds, 1 = one bound, 2 = no bounds
    };
    std::vector<Candidate> candidates;

    for (const auto& var : allVars) {
        const IntDomain* d = domains.getDomain(var);
        Candidate c{var, false, false, 0, 0, 0, 2};
        if (d) {
            c.hasLower = d->hasLower;
            c.hasUpper = d->hasUpper;
            if (c.hasLower) c.lower = d->lower.value;
            if (c.hasUpper) c.upper = d->upper.value;
            if (c.hasLower && c.hasUpper) {
                c.rangeSize = c.upper - c.lower;
                c.priority = 0;
                // Skip singleton domains (already fixed)
                if (c.rangeSize <= 0) continue;
            } else if (c.hasLower || c.hasUpper) {
                c.priority = 1;
            }
        }
        candidates.push_back(c);
    }

    if (candidates.empty()) return std::nullopt;

    // I1: XOLVER_NIA_LS_BRANCH_HINT (default-OFF). When local search has
    // populated varActivity (vars that participated in improving moves in
    // recent SLS rounds), use that as a secondary sort key between
    // priority and rangeSize. The rationale (Yices2LS pattern): a variable
    // that local search keeps perturbing in a UNSAT-leaning region is
    // structurally hot — branching on it is more likely to expose the
    // conflict the SAT engine needs. Heuristic only — never affects
    // soundness; the branch lemma is still a tautology (x<=k ∨ x>=k+1).
    static const bool lsBranchHint = [] {
        const char* e = std::getenv("XOLVER_NIA_LS_BRANCH_HINT");
        return e && *e && *e != '0';
    }();
    const auto& lsAct = localSearch_.lsContext().varActivity;
    auto activityOf = [&lsAct](const std::string& v) -> uint64_t {
        auto it = lsAct.find(v);
        return it == lsAct.end() ? 0u : it->second;
    };

    // Sort: priority first, optional LS-activity tiebreak, then larger range size
    std::sort(candidates.begin(), candidates.end(),
        [&](const Candidate& a, const Candidate& b) {
            if (a.priority != b.priority) return a.priority < b.priority;
            if (lsBranchHint) {
                uint64_t aAct = activityOf(a.var);
                uint64_t bAct = activityOf(b.var);
                if (aAct != bAct) return aAct > bAct;
            }
            return a.rangeSize > b.rangeSize;
        });

    for (const auto& cand : candidates) {
        mpz_class k;
        if (cand.hasLower && cand.hasUpper) {
            k = (cand.lower + cand.upper) / 2;
        } else if (cand.hasLower) {
            k = cand.lower;
        } else if (cand.hasUpper) {
            k = cand.upper - 1;
        } else {
            // Unbounded: only center split at k=0
            k = 0;
        }

        const IntDomain* d = domains.getDomain(cand.var);
        bool hasBothBounds = d && d->hasLower && d->hasUpper;
        bool isUnbounded = !cand.hasLower && !cand.hasUpper;
        int& count = branchCountPerVar_[cand.var];
        if (isUnbounded && count >= MAX_UNBOUNDED_SPLITS) continue;
        if (!hasBothBounds && !isUnbounded && count >= MAX_SINGLE_BOUND_SPLITS) continue;

        // Duplicate suppression: skip if already emitted
        BranchSplitKey key{cand.var, k};
        if (emittedSplits_.count(key)) continue;

        PolyId xPoly = kernel_->mkVar(kernel_->getOrCreateVar(cand.var));

        // x <= k
        SatLit litLeq = registry_->getOrCreatePolynomialAtom(
            xPoly, Relation::Leq, mpq_class(k), TheoryId::NIA);

        // x >= k+1
        SatLit litGeq = registry_->getOrCreatePolynomialAtom(
            xPoly, Relation::Geq, mpq_class(k + 1), TheoryId::NIA);

        TheoryLemma lemma{{litLeq, litGeq}};

        if (lemmaDb.contains(lemma)) continue;
        lemmaDb.insertIfNew(lemma);
        emittedSplits_.insert(key);
        ++count;

        return lemma;
    }

    return std::nullopt;
}

TheoryCheckResult NiaSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {
    // Phase D: interface eq changes the combined-state signature.
    dispatchCacheValid_ = false;
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

    if (ifaceLifecycleEnabled_) {
        // Keep the interface equality OUT of active_/trail_/activeSet_; record
        // it (with its converted constraint) for level-correct backtracking and
        // for merge at stageNormalize. See member doc on ifaceLifecycleEnabled_.
        interfaceEqualities_.push_back({a, b, reason, level, cc.diff, Relation::Eq});
        return TheoryCheckResult::consistent();
    }
    size_t oldSize = active_.size();
    active_.push_back({cc.diff, Relation::Eq, reason});
    trail_.push_back({level, oldSize});
    interfaceEqualities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

TheoryCheckResult NiaSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {
    // Phase D: interface diseq changes the combined-state signature.
    dispatchCacheValid_ = false;
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

    if (ifaceLifecycleEnabled_) {
        interfaceDisequalities_.push_back({a, b, reason, level, cc.diff, Relation::Neq});
        return TheoryCheckResult::consistent();
    }
    size_t oldSize = active_.size();
    active_.push_back({cc.diff, Relation::Neq, reason});
    trail_.push_back({level, oldSize});
    interfaceDisequalities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

std::optional<RealValue>
NiaSolver::sharedTermArithValue(SharedTermId s) const {
    // Gated default-ON for QF_ANIA / QF_AUFNIA: without this, the combination
    // layer's model-based arrangement (TheoryManager §4) skips every shared
    // term because the loop's `if (!v) continue;` fires when the arith solver
    // returns nullopt (the inherited base default). Closing this gap is what
    // lets array combination ever emit a same-value scalar-arrangement split
    // for QF_ANIA cases (the long-standing 0/157 hole — iter#1-#4 emitted
    // shared-eqs into a layer that wasn't running). Opt-out via
    // XOLVER_NIA_SHARED_ARITH_VALUE=0 if the arrangement+nonlinear-branch
    // interaction starts to oscillate.
    static const bool enabled =
        env::paramInt("XOLVER_NIA_SHARED_ARITH_VALUE", 1) != 0;
    if (!enabled) return std::nullopt;

    if (!sharedTermRegistry_ || !coreIr_) return std::nullopt;
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return std::nullopt;
    const auto& expr = coreIr_->get(st->coreExpr);

    // Constants — return the literal value directly. Mirrors LiaSolver's
    // constant handling so an arithmetic constant participates in the
    // arrangement on equal terms with a variable bound to that value.
    if (expr.kind == Kind::ConstInt) {
        if (auto* iv = std::get_if<int64_t>(&expr.payload.value)) {
            return RealValue::fromMpq(mpq_class(*iv));
        }
        if (auto* sv = std::get_if<std::string>(&expr.payload.value)) {
            return RealValue::fromMpq(mpqFromString(*sv));
        }
    }
    if (expr.kind == Kind::ConstReal) {
        if (auto* sv = std::get_if<std::string>(&expr.payload.value)) {
            return RealValue::fromMpq(mpqFromString(*sv));
        }
    }

    // Variables — read the latest NIA model entry. currentModel_ holds the
    // current check()'s candidate model; lastValidatedFarkasModel_ is the
    // fallback Farkas-Or witness that survives reset/backtrack. Either is
    // sound for the arrangement's "what value does NIA think this term has
    // right now?" query — the arrangement only emits TAUTOLOGY splits
    // `(a = b) ∨ ¬(a = b)`, so a wrong-guess split costs one SAT-layer commit
    // cycle but never a soundness violation. ModelValidator at the
    // Solver::Impl boundary still catches a globally-inconsistent model.
    if (expr.kind != Kind::Variable ||
        !std::holds_alternative<std::string>(expr.payload.value)) {
        // Iter#30: compound shared terms (e.g. `(+ i 1)` as an array index)
        // had no value path here pre-iter#30 — returned nullopt → array-
        // combination arrangement skipped them entirely. iter#28-29 opened
        // the channel; this opens the SOURCE for compound terms by
        // recursively evaluating Add/Sub/Mul/Neg over the current NIA
        // model. SOUND: this only returns a value when EVERY leaf evaluates
        // (Variable found in model, Const literal); on any unresolved leaf
        // or unsupported kind, falls through to nullopt → arrangement
        // safely skips the term (same as pre-iter#30 behavior).
        // Recursion depth bounded at 32 (anti-pathological-DAG guard).
        const IntegerModel* src = nullptr;
        if (currentModel_)                  src = &*currentModel_;
        else if (lastValidatedFarkasModel_) src = &*lastValidatedFarkasModel_;
        if (!src) return std::nullopt;
        std::function<std::optional<mpz_class>(ExprId, int)> ev =
            [&](ExprId e, int depth) -> std::optional<mpz_class> {
                if (depth > 32 || e == NullExpr || e >= coreIr_->size())
                    return std::nullopt;
                const auto& n = coreIr_->get(e);
                if (n.kind == Kind::ConstInt) {
                    if (auto* iv = std::get_if<int64_t>(&n.payload.value))
                        return mpz_class(*iv);
                    if (auto* sv = std::get_if<std::string>(&n.payload.value)) {
                        try { return mpz_class(*sv); }
                        catch (...) { return std::nullopt; }
                    }
                    return std::nullopt;
                }
                if (n.kind == Kind::Variable) {
                    if (auto* nm = std::get_if<std::string>(&n.payload.value)) {
                        auto it = src->find(*nm);
                        if (it == src->end()) return std::nullopt;
                        return it->second;
                    }
                    return std::nullopt;
                }
                if (n.kind == Kind::Add) {
                    mpz_class acc = 0;
                    for (ExprId c : n.children) {
                        auto cv = ev(c, depth + 1);
                        if (!cv) return std::nullopt;
                        acc += *cv;
                    }
                    return acc;
                }
                if (n.kind == Kind::Sub) {
                    if (n.children.empty()) return std::nullopt;
                    auto fv = ev(n.children[0], depth + 1);
                    if (!fv) return std::nullopt;
                    mpz_class acc = *fv;
                    for (size_t i = 1; i < n.children.size(); ++i) {
                        auto cv = ev(n.children[i], depth + 1);
                        if (!cv) return std::nullopt;
                        acc -= *cv;
                    }
                    return acc;
                }
                if (n.kind == Kind::Neg) {
                    if (n.children.size() != 1) return std::nullopt;
                    auto cv = ev(n.children[0], depth + 1);
                    if (!cv) return std::nullopt;
                    return -*cv;
                }
                if (n.kind == Kind::Mul) {
                    mpz_class acc = 1;
                    for (ExprId c : n.children) {
                        auto cv = ev(c, depth + 1);
                        if (!cv) return std::nullopt;
                        acc *= *cv;
                    }
                    return acc;
                }
                return std::nullopt;
            };
        auto val = ev(st->coreExpr, 0);
        if (!val) return std::nullopt;
        return RealValue::fromMpz(*val);
    }
    const std::string& name = std::get<std::string>(expr.payload.value);
    const IntegerModel* src = nullptr;
    if (currentModel_)                  src = &*currentModel_;
    else if (lastValidatedFarkasModel_) src = &*lastValidatedFarkasModel_;
    // Iter#25 diag: count ALL invocations + classification (null-model vs
    // found vs missing-from-model). Set XOLVER_NIA_ARITH_VALUE_DIAG=1.
    static const bool diag =
        std::getenv("XOLVER_NIA_ARITH_VALUE_DIAG") != nullptr;
    static long callCount = 0;
    static long nullModelCount = 0;
    static long missingNameCount = 0;
    static long foundCount = 0;
    if (diag) {
        ++callCount;
        if (!src) ++nullModelCount;
        else if (src->find(name) == src->end()) ++missingNameCount;
        else ++foundCount;
        if (callCount % 100 == 1) {
            std::fprintf(stderr,
                         "[NIA-ARITH-VALUE] calls=%ld null-model=%ld missing-name=%ld found=%ld\n",
                         callCount, nullModelCount, missingNameCount, foundCount);
        }
    }
    if (!src) return std::nullopt;
    auto it = src->find(name);
    if (it == src->end()) return std::nullopt;
    return RealValue::fromMpz(it->second);
}

std::vector<TheorySolver::SharedEqualityPropagation>
NiaSolver::getDeducedSharedEqualities() {
    // Nelson-Oppen fixed-value seam: when two shared integer variables both
    // have their NIA domain pinned to the same singleton {v}, propagate the
    // equality to EUF so the e-graph can fire array/UF axioms (read-over-
    // write, congruence) that depend on the equality.
    //
    // Without this, QF_ANIA / QF_AUFNIA combination instances where the
    // equality is implied by NIA bounds (e.g. `a = b` follows from
    // `a >= n /\ a <= n /\ b >= n /\ b <= n`) are unreachable: NIA never
    // tells EUF, EUF never closes the read-over-write, and the combined
    // verdict stays Unknown. NiaSolver previously returned {} unconditionally,
    // closing this seam entirely (the LIA path was the only one open).
    //
    // SOUND: a pair is emitted only when both vars' integer domains pin them
    // to the same value, and the propagation reasons are the (deduped) union
    // of the four bound-reason literals (lo_a, hi_a, lo_b, hi_b). If any
    // bound is later relaxed by backtrack, the propagation's reason becomes
    // unsatisfied and the SAT layer retracts it through normal conflict
    // analysis. Same proof contract as LiaSolver::getDeducedSharedEqualities'
    // fixed-value loop.
    if (!sharedTermRegistry_) return {};

    struct Entry {
        SharedTermId stId;
        std::vector<SatLit> reasons;
    };
    // map<mpz_class, ...> for determinism (autotuner / oracle reproducibility).
    std::map<mpz_class, std::vector<Entry>> groups;

    for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
        std::string name = getVarNameForSharedTerm(stId);
        if (name.empty()) continue;
        const IntDomain* d = domains_.getDomain(name);
        if (!d) continue;
        if (!(d->hasLower && d->hasUpper)) continue;
        if (d->lower.value != d->upper.value) continue;

        std::vector<SatLit> reasons;
        reasons.insert(reasons.end(), d->lower.reasons.begin(),
                       d->lower.reasons.end());
        reasons.insert(reasons.end(), d->upper.reasons.begin(),
                       d->upper.reasons.end());
        std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
            return a.var < b.var || (a.var == b.var && a.sign < b.sign);
        });
        reasons.erase(std::unique(reasons.begin(), reasons.end(),
                                  [](SatLit a, SatLit b) {
            return a.var == b.var && a.sign == b.sign;
        }), reasons.end());

        groups[d->lower.value].push_back({stId, std::move(reasons)});
    }

    std::vector<TheorySolver::SharedEqualityPropagation> result;
    for (auto& [val, entries] : groups) {
        if (entries.size() < 2) continue;
        for (size_t i = 0; i < entries.size(); ++i) {
            for (size_t j = i + 1; j < entries.size(); ++j) {
                std::vector<SatLit> combined;
                combined.insert(combined.end(), entries[i].reasons.begin(),
                                entries[i].reasons.end());
                combined.insert(combined.end(), entries[j].reasons.begin(),
                                entries[j].reasons.end());
                std::sort(combined.begin(), combined.end(),
                          [](SatLit a, SatLit b) {
                    return a.var < b.var || (a.var == b.var && a.sign < b.sign);
                });
                combined.erase(std::unique(combined.begin(), combined.end(),
                                           [](SatLit a, SatLit b) {
                    return a.var == b.var && a.sign == b.sign;
                }), combined.end());
                result.push_back(TheorySolver::SharedEqualityPropagation{
                    entries[i].stId, entries[j].stId, std::move(combined)});
            }
        }
    }

    // ---------------------------------------------------------------------
    // Var-var implied equalities (port of LIA's assertedVarEqualityReason).
    //
    // Two shared integer variables can be forced equal by NIA-asserted
    // linear atoms even when neither domain pins to a constant: an explicit
    // equality atom `c*x - c*y = k` with `k = 0`, or complementary
    // inequalities `c*(x-y) >= k AND c*(x-y) <= k` collapsing to a single
    // point. For each pair of shared vars (a, b), walk the active trail
    // accumulating bounds on `d = na - nb` from atoms whose polynomial is
    // exactly a 2-variable linear difference; if the accumulated interval
    // collapses to {0}, emit the propagation with the two pinning literals.
    //
    // SOUND:
    //   1. Exact-pins-only: only emit when the accumulated lo == up == 0
    //      after iterating all 2-var difference atoms on the trail. Strict
    //      bounds (Lt/Gt) are skipped (they don't pin an equality).
    //   2. Complete explanation: reasons = the two pinning literals (loLit,
    //      upLit) — those are the SAT literals whose retraction unblocks
    //      the derived equality. SAT-CDCL will retract the propagation
    //      automatically when either reason becomes unassigned.
    //   3. Backtrack invalidation: state_.trail entries are dropped by the
    //      base class's backtrackToLevel; the next getDeducedSharedEqualities
    //      call rescans fresh.
    //   4. Deduped against the fixed-value loop above (a pair already pinned
    //      by both vars being singleton-domain is not re-emitted here).
    //   5. PolynomialAtomPayload with an algebraic (non-rational) rhs is
    //      skipped — over-conservative but never wrong.
    if (sharedTermRegistry_) {
        struct SV { SharedTermId stId; std::string name; };
        std::vector<SV> svs;
        for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
            std::string name = getVarNameForSharedTerm(stId);
            if (name.empty()) continue;
            svs.push_back({stId, std::move(name)});
        }

        if (svs.size() >= 2) {
            auto pairKey = [](SharedTermId a, SharedTermId b) -> uint64_t {
                SharedTermId lo = a < b ? a : b;
                SharedTermId hi = a < b ? b : a;
                return (static_cast<uint64_t>(lo) << 32)
                     | static_cast<uint32_t>(hi);
            };
            std::unordered_set<uint64_t> emittedPair;
            for (const auto& p : result) emittedPair.insert(pairKey(p.a, p.b));

            for (size_t i = 0; i < svs.size(); ++i) {
                for (size_t j = i + 1; j < svs.size(); ++j) {
                    if (emittedPair.count(pairKey(svs[i].stId, svs[j].stId)))
                        continue;
                    const std::string& na = svs[i].name;
                    const std::string& nb = svs[j].name;

                    bool haveLo = false, haveUp = false;
                    mpq_class lo = 0, up = 0;
                    SatLit loLit{}, upLit{};

                    for (const auto& e : state_.trail) {
                        const auto* p = std::get_if<PolynomialAtomPayload>(
                                            &e.atom.payload);
                        if (!p) continue;
                        if (!p->rhs.isRational()) continue;

                        auto vars = kernel_->variables(p->poly);
                        if (vars.size() != 2) continue;
                        bool hasA = false, hasB = false;
                        for (const auto& v : vars) {
                            if (v == na) hasA = true;
                            else if (v == nb) hasB = true;
                        }
                        if (!hasA || !hasB) continue;

                        auto tOpt = kernel_->terms(p->poly);
                        if (!tOpt) continue;
                        mpz_class cA = 0, cB = 0, k = 0;
                        bool ok = true;
                        for (const auto& m : *tOpt) {
                            if (m.powers.empty()) {
                                k += m.coefficient;
                            } else if (m.powers.size() == 1
                                       && m.powers[0].second == 1) {
                                std::string vn(
                                    kernel_->varName(m.powers[0].first));
                                if (vn == na)      cA += m.coefficient;
                                else if (vn == nb) cB += m.coefficient;
                                else { ok = false; break; }
                            } else {
                                ok = false; break;  // nonlinear monomial
                            }
                        }
                        if (!ok) continue;
                        if (cA == 0 || cA != -cB) continue;

                        Relation rel = e.value ? p->rel
                                               : negateRelation(p->rel);
                        if (rel == Relation::Neq) continue;  // never pins
                        const mpq_class& rhsQ = p->rhs.asRational();
                        // poly = cA*(na - nb) + k ; rel rhsQ
                        // => d = na - nb satisfies  cA*d  rel  (rhsQ - k)
                        // => d rel'  (rhsQ - k)/cA  with rel' flipped if cA<0
                        mpq_class bnd = (rhsQ - mpq_class(k)) / mpq_class(cA);
                        bool flip = (cA < 0);
                        auto addLower = [&](const mpq_class& v, SatLit lit) {
                            if (!haveLo || v > lo) {
                                lo = v; loLit = lit; haveLo = true;
                            }
                        };
                        auto addUpper = [&](const mpq_class& v, SatLit lit) {
                            if (!haveUp || v < up) {
                                up = v; upLit = lit; haveUp = true;
                            }
                        };
                        switch (rel) {
                            case Relation::Eq:
                                addLower(bnd, e.lit);
                                addUpper(bnd, e.lit);
                                break;
                            case Relation::Leq:
                                if (!flip) addUpper(bnd, e.lit);
                                else       addLower(bnd, e.lit);
                                break;
                            case Relation::Geq:
                                if (!flip) addLower(bnd, e.lit);
                                else       addUpper(bnd, e.lit);
                                break;
                            case Relation::Lt:
                            case Relation::Gt:
                            default:
                                break;  // strict — does not pin
                        }
                    }

                    if (haveLo && haveUp && lo == 0 && up == 0) {
                        std::vector<SatLit> reasons;
                        reasons.push_back(loLit);
                        if (!(upLit == loLit)) reasons.push_back(upLit);
                        std::sort(reasons.begin(), reasons.end(),
                                  [](SatLit a, SatLit b) {
                            return a.var < b.var
                                || (a.var == b.var && a.sign < b.sign);
                        });
                        reasons.erase(std::unique(reasons.begin(), reasons.end(),
                                                  [](SatLit a, SatLit b) {
                            return a.var == b.var && a.sign == b.sign;
                        }), reasons.end());
                        emittedPair.insert(
                            pairKey(svs[i].stId, svs[j].stId));
                        result.push_back(TheorySolver::SharedEqualityPropagation{
                            svs[i].stId, svs[j].stId, std::move(reasons)});
                    }
                }
            }
        }
    }

    // Iter#25 diag: count ALL invocations + propagation sizes. Set
    // XOLVER_NIA_SHARED_EQ_DIAG=1 to see periodic counter. This proves
    // master directive #1: does NIA emit shared-eqs at all on QF_ANIA?
    static long callCount = 0;
    static long totalEmitted = 0;
    if (std::getenv("XOLVER_NIA_SHARED_EQ_DIAG")) {
        ++callCount;
        totalEmitted += result.size();
        if (callCount % 20 == 1 || !result.empty()) {
            std::fprintf(stderr,
                         "[NIA-SHARED-EQ] calls=%ld emitted-this=%zu total=%ld\n",
                         callCount, result.size(), totalEmitted);
        }
    }
    return result;
}

std::optional<TheorySolver::TheoryModel> NiaSolver::getModel() const {
    // Prefer currentModel_; fall back to lastValidatedFarkasModel_ which
    // survives reset()/backtrack and represents the last validator-
    // confirmed Farkas-Or witness. Used by Solver.cpp's Unknown-fallback
    // to recover a SAT verdict when SAT-CDCL timed out.
    const IntegerModel* src = nullptr;
    if (currentModel_)               src = &*currentModel_;
    else if (lastValidatedFarkasModel_) src = &*lastValidatedFarkasModel_;
    if (!src) return std::nullopt;
    TheoryModel model;
    for (const auto& [name, value] : *src) {
        model.assignments[name] = value.get_str();
        model.numericAssignments.insert({name, RealValue::fromMpz(value)});
    }
    if (model.assignments.empty()) return std::nullopt;
    return model;
}

} // namespace xolver
