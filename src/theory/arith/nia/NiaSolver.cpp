#include "theory/arith/nia/NiaSolver.h"
#include "theory/arith/nia/NiaSolverDetail.h"  // collectVars / dispatch-signature helpers (shared across split TUs)
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
#include "theory/arith/nia/search/NiaLinearDecider.h"  // embedded complete-LIA (nia.linear-decide)
#include "theory/arith/nia/reasoners/OmegaTest.h"        // nia.omega: sound linear-integer UNSAT
#include "theory/arith/nia/reasoners/SmallPrimeModular.h" // nia.small-prime-modular: GF(p) schedule
#include "theory/arith/nia/reasoners/IntBoundProp.h"      // nia.int-bound-prop: integer interval refutation
#include "theory/arith/linearizer/NonlinearTermAbstraction.h"
#include "theory/arith/linear/LinearConstraintNormalizer.h"
#include "theory/core/LogicFeatureDetector.h"
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
    // nia.linear-prop (XOLVER_NIA_LINEAR_PROP, default-OFF). Standard+Full so it
    // fires during search at PARTIAL assignments (the cs_* QF_ANIA cluster never
    // reaches a Full-effort model check within budget — the only place the
    // existing nia.linear-decide could run). Placed right after normalize so it
    // reads the fresh normalized_ set. Emits sound Farkas conflicts + fixed-value
    // entailments over the all-linear active core.
    linearPropEnabled_ = env::paramInt("XOLVER_NIA_LINEAR_PROP", 0) != 0;
    add("nia.linear-prop",    &NiaSolver::stageLinearProp);
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
    // nia.linear-decide (DEFAULT-OFF; XOLVER_NIA_LINEAR_DECIDE=1 enables). Runs
    // FIRST among the Full-effort stages — after normalize built active_, before
    // the heavy/escalating stages (presolve … bit-blast … local-search). When
    // active_ is entirely linear it hands the COMPLETE normalized constraint set
    // to an embedded complete-LIA decision (simplex + integrality repair +
    // branch-and-bound) and returns a validated SAT model; on UNSAT/Unknown it
    // falls through so the existing (sound) stages decide. SAT-only ⇒ no
    // wrong-UNSAT (invariant 7). Default-OFF: it currently cracks small/
    // repair-tractable linear-combination SAT cases but NOT the large-coefficient
    // mod cluster (sum10-class), where the LP is degenerate and B&B walks; until
    // it nets positive on a differential, the B&B overhead before bit-blast
    // fallthrough is a regression risk, so it stays opt-in.
    linearDecideEnabled_ = env::paramInt("XOLVER_NIA_LINEAR_DECIDE", 0) != 0;
    addFull("nia.linear-decide", &NiaSolver::stageLinearDecide);
    enableOmega_ = xolver::env::flag("XOLVER_NIA_OMEGA");
    addFull("nia.omega", &NiaSolver::stageOmega);
    // nia.small-prime-modular: cheap GF(p) congruence refutation over the equality
    // subsystem. Standard+Full (unlike Omega) so it can prune EARLY, before complete
    // models — the gap the Full-effort-only Dio/Smith-NF reasoner leaves open.
    enableSmallPrimeModular_ = xolver::env::flag("XOLVER_NIA_SMALL_PRIME_MODULAR");
    add("nia.small-prime-modular", &NiaSolver::stageSmallPrimeModular);
    // nia.int-bound-prop: integer interval contraction over the equalities seeded by
    // the asserted single-variable bounds — refutes bound×equality integer-infeasibility
    // (e.g. x=2y ∧ x=1) that the equalities-only modular reasoner misses.
    enableIntBoundProp_ = xolver::env::flag("XOLVER_NIA_INT_BOUND_PROP");
    add("nia.int-bound-prop", &NiaSolver::stageIntBoundProp);
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
    if (xolver::env::flag("XOLVER_NIA_NO_BITBLAST"))
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
    if (xolver::env::flag("XOLVER_NIA_GROBNER"))
        enableGroebner_ = true;

    // Interval contraction fixpoint over the existing icp/ engine (default-ON).
    // Sound: only narrows domains via valid bound propagation; UNSAT reported
    // solely from a contractor conflict or an emptied domain (invariant 7).

    // Integer-aware CDCAC (default-OFF). Sound: a CDCAC covering-UNSAT over the
    // real relaxation implies integer-UNSAT (ℤⁿ⊆ℝⁿ; gated by CdcacCore's own
    // unsatTrustworthy_); a CDCAC SAT sample is accepted only when every
    // coordinate is an exact integer AND it passes IntegerModelValidator.
    if (xolver::env::flag("XOLVER_NIA_CDCAC"))
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
    entailmentProps_.clear();
    entailmentEmittedKeys_.clear();
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
        static const bool oppDiag = xolver::env::diag("NIA_OPP_DIAG");
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
    // nia.linear-prop: drop any undrained entailments and reset the dedup so a
    // fresh SAT branch can re-emit pins under its own reasons. The emitted
    // clauses already in the SAT core stay (they are global tautologies).
    entailmentProps_.clear();
    entailmentEmittedKeys_.clear();
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

// collectVars() moved to NiaSolverDetail.h so the split NiaSolver_*.cpp TUs can
// share it (union of variable names over a set of normalized NIA constraints).

// ---------------------------------------------------------------------------
// Reasoner pipeline stages (Phase 2). Verbatim decomposition of the former
// linear check() body. Each stage returns nullopt to fall through to the
// next, or a TheoryCheckResult to stop. `normalized_` and `domains_` are the
// shared state threaded across stages.
// ---------------------------------------------------------------------------


std::vector<TheoryLemma> NiaSolver::takeEntailmentPropagations() {
    if (!linearPropEnabled_) return {};
    return std::move(entailmentProps_);
}

// Phase D — FNV-1a hash of the active_ signature: count + sequence of
// (satVar, sign) drawn from state_.trail + interface-eq/diseq counts.
// Cheap, deterministic, collision-resistant enough for the cache use
// case (a stale hit would only re-run the pipeline next call, never a
// soundness concern — the cache only short-circuits identical inputs).
// fnv1aMix / computeDispatchSignature moved to NiaSolverDetail.h (dispatch-cache
// state fingerprint), shared across the split NiaSolver_*.cpp translation units.


void NiaSolver::setModEqConstFacts(const ModEqConstFactList& facts) {
    // Track A Phase 1.3 — Solver::Impl hands off facts captured from
    // IntDivModLowerer here. Each fact's `reason` SatLit is still
    // unset (atomization is done after preprocess); the stage method
    // resolves it via TheoryAtomRegistry per call. (const-ref to match the
    // polymorphic TheorySolver::setModEqConstFacts hook; set once at setup.)
    modEqConstFacts_ = facts;
}


} // namespace xolver
