#include "theory/arith/nia/NiaSolver.h"
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
#include "theory/arith/nra/nla/NlaCutsRunner.h"           // Stage 3 Phase C-3
#include "theory/arith/poly/RationalPolynomial.h"          // Stage 3 Phase C-3
#endif
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/presolve/Presolve.h"
#include "theory/arith/search/CompleteFiniteDomainEnumerator.h"
#include "theory/core/TheoryLemmaDatabase.h"
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
      modularResidue_(*kernel_) {
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
    // Phase D — dispatch-cache lookup at the FRONT of the pipeline. On a
    // signature hit, skip the entire 16-stage pipeline. Default-OFF flag
    // XOLVER_NIA_DISPATCH_CACHE. No-op when the flag is unset.
    add("nia.dispatch-cache", &NiaSolver::stageDispatchCacheLookup);
    add("nia.normalize",      &NiaSolver::stageNormalize);
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
    if (const char* e = std::getenv("XOLVER_NIA_PRESOLVE_FULL"); e && *e && *e != '0')
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
    // HYB-3 (master 2026-06-02 H5 finding) — Standard+Full registration
    // mirrors stageBitBlastEarly / stageLocalSearchEarly. On SAT14-class
    // inputs, Full-effort is unreachable in budget; HYB-3 must fire at
    // Standard effort to have any chance. Gated default-OFF.
    add("nia.hyb-bb-ls", &NiaSolver::stageHybridBbLs);
    add("nia.pending-lemma",  &NiaSolver::stagePendingLemma);
    // Phase D — dispatch-cache record at the TAIL (right before branch).
    // Reaching here means every earlier stage returned nullopt, so the
    // pipeline will fall through to consistent(). Memoize the active_
    // signature so the next identical call hits stageDispatchCacheLookup.
    add("nia.dispatch-cache-record", &NiaSolver::stageDispatchCacheRecord);
    add("nia.branch",         &NiaSolver::stageBranch);

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
    if (const char* e = std::getenv("XOLVER_NIA_IFACE_LIFECYCLE"); e && *e && *e != '0')
        ifaceLifecycleEnabled_ = true;
}

void NiaSolver::onReset() {
    // Base clears state_.trail + its pending slot; NIA clears its own
    // polynomial stack, active literal set, level-tagged pendings, and
    // combination state.
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
    PresolveEngine presolve(kernel_.get(), /*integerDomain=*/true);
    bool feasible = true;
    for (const auto& c : normalized_) {
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) { feasible = false; break; }
        presolve.addAtom(*rp, c.rel, c.reason);
    }
    if (feasible) {
        auto pr = presolve.run();
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
    static const bool earlyEnabled = [] {
        const char* e = std::getenv("XOLVER_NIA_BB_EARLY");
        return e && *e && *e != '0';
    }();
    if (!earlyEnabled) return std::nullopt;
    if (!enableBitBlast_) return std::nullopt;
    if (std::getenv("XOLVER_NIA_NO_BITBLAST")) return std::nullopt;
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

std::optional<TheoryCheckResult> NiaSolver::stageLocalSearch(TheoryLemmaStorage&, TheoryEffort) {
    // Local search SAT finder (try before emitting pending linear lemmas)
    if (auto model = localSearch_.tryFindModel(normalized_, domains_)) {
        if (validator_.validate(*model, normalized_) == IntegerModelValidator::Result::Valid) {
            currentModel_ = *model;
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
    static const size_t maxB = [] {
        if (const char* e = std::getenv("XOLVER_NIA_HYB_BB_LS_MAX_B"))
            return static_cast<size_t>(std::atol(e));
        return static_cast<size_t>(10);
    }();
    if (pr.boundedCount() == 0 || pr.boundedCount() > maxB) return std::nullopt;
    if (pr.unboundedCount() < pr.boundedCount() * 3) return std::nullopt;

    // K = number of random B-samples to try.
    static const int K = [] {
        if (const char* e = std::getenv("XOLVER_NIA_HYB_BB_LS_K"))
            return std::atoi(e);
        return 5;
    }();
    static const long probeMs = [] {
        if (const char* e = std::getenv("XOLVER_NIA_HYB_BB_LS_PROBE_MS"))
            return std::atol(e);
        return 500L;
    }();

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
    static const long earlyBudgetMs = [] {
        if (const char* e = std::getenv("XOLVER_NIA_LS_EARLY_BUDGET_MS"))
            return std::atol(e);
        return 200L;
    }();
    static const long earlyTotalMs = [] {
        if (const char* e = std::getenv("XOLVER_NIA_LS_EARLY_TOTAL_MS"))
            return std::atol(e);
        return 5000L;
    }();
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

std::vector<TheorySolver::SharedEqualityPropagation>
NiaSolver::getDeducedSharedEqualities() {
    return {};
}

std::optional<TheorySolver::TheoryModel> NiaSolver::getModel() const {
    if (!currentModel_) return std::nullopt;
    TheoryModel model;
    for (const auto& [name, value] : *currentModel_) {
        model.assignments[name] = value.get_str();
        model.numericAssignments.insert({name, RealValue::fromMpz(value)});
    }
    if (model.assignments.empty()) return std::nullopt;
    return model;
}

} // namespace xolver
