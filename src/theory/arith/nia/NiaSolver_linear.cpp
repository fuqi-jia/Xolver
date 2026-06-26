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

#include <unordered_set>
#include <cstdlib>
namespace xolver {

// NOTE: This translation unit was split out of NiaSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

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

// nia.linear-decide — complete LINEAR decision for an all-linear active set,
// producing a SAT model. NIA owns the linear atoms in every NIA logic (the
// Purifier tags arith atoms NIA even in combination, so the registered LIA
// sibling never receives them — verified: XOLVER_NIA_LINEAR_SHORTCUT defers to
// LIA and yields `unknown`, not `sat`). NIA's non-bit-blast stages can refute
// small linear systems but have no complete multi-variable feasibility+model
// procedure; bit-blast is the only model-finder and it escalates bit-width
// (growing CNF) and times out in array combination. This stage embeds a full
// LiaSolver (simplex + integer branch-and-bound + integrality repair), replays
// the active trail into it, and — ONLY on a validated SAT integer model —
// returns Consistent with that model. UNSAT/Unknown fall through to the existing
// (sound) stages: we never emit UNSAT here, so there is zero wrong-UNSAT risk
// (invariant 7). The harvested model is re-checked by IntegerModelValidator
// against NIA's own normalized constraints (invariant 1, defense in depth).
std::optional<TheoryCheckResult> NiaSolver::stageLinearDecide(
    TheoryLemmaStorage&, TheoryEffort effort) {
    if (!linearDecideEnabled_) return std::nullopt;
    // Model construction needs a complete assignment ⇒ Full effort only
    // (registered via addFull, but assert intent).
    if (effort != TheoryEffort::Full) return std::nullopt;
    if (active_.empty()) return std::nullopt;   // stagePending handles empty
    if (!registry_) return std::nullopt;

    // All active atoms must be LINEAR (total degree ≤ 1).
    for (const auto& a : active_) {
        auto terms = kernel_->terms(a.poly);
        if (!terms) return std::nullopt;        // can't decompose → defer
        for (const auto& term : *terms) {
            int total = 0;
            for (const auto& [vid, exp] : term.powers) {
                (void)vid;
                total += exp;
                if (total > 1) return std::nullopt;   // nonlinear → defer
            }
        }
    }

    if (xolver::env::diag("XOLVER_NIA_LINDECIDE_DIAG"))
        std::fprintf(stderr, "[LINDECIDE] stage fired: active=%zu normalized=%zu trail=%zu\n",
                     active_.size(), normalized_.size(), state_.trail.size());

    // Delegate to the embedded complete-LIA decision (own TU). It returns either
    // a validated integer model (SAT), or — when the asserted linear atoms are
    // jointly infeasible at the LP root — a Farkas conflict over the REAL
    // asserted SAT literals, which we return so the SAT search is pruned. The
    // conflict is a genuine infeasibility of the current trail (sound; never a
    // global UNSAT claim beyond what the linear atoms entail).
    if (!linDecider_) linDecider_ = std::make_unique<NiaLinearDecider>();
    std::optional<TheoryConflict> conflict;
    auto im = linDecider_->decide(registry_, *kernel_, normalized_, validator_, &conflict);
    if (im) {
        currentModel_ = std::move(*im);
        return TheoryCheckResult::consistent();
    }
    if (conflict) return TheoryCheckResult::mkConflict(std::move(*conflict));
    return std::nullopt;
}

// nia.linear-prop — Standard+Full linear propagation over the all-linear active
// core. Returns a sound Farkas conflict (prune) on linear infeasibility, else
// buffers fixed-value entailments (drained by takeEntailmentPropagations). Never
// claims SAT (no model returned), so zero wrong-UNSAT/wrong-SAT risk (the
// conflict is over real asserted reasons; entailments are global tautologies).
std::optional<TheoryCheckResult> NiaSolver::stageLinearProp(
    TheoryLemmaStorage&, TheoryEffort effort) {
    if (!linearPropEnabled_) return std::nullopt;
    if (active_.empty()) return std::nullopt;
    if (!registry_) return std::nullopt;
    // normalized_ is produced by the immediately-preceding nia.normalize stage;
    // in combination it ALSO carries merged interface (dis)equalities, so it is
    // ≥ active_.size(). Require it non-empty (normalize ran) — not equal.
    if (normalized_.empty()) return std::nullopt;

    // All active atoms must be LINEAR (total degree ≤ 1) — otherwise the simplex
    // would drop nonlinear obligations and could mis-propagate.
    for (const auto& a : active_) {
        auto terms = kernel_->terms(a.poly);
        if (!terms) return std::nullopt;
        for (const auto& term : *terms) {
            int total = 0;
            for (const auto& [vid, exp] : term.powers) {
                (void)vid;
                total += exp;
                if (total > 1) return std::nullopt;
            }
        }
    }

    if (!linDecider_) linDecider_ = std::make_unique<NiaLinearDecider>();

    // Asserted-literal map for the soundness firewall + the "already decided"
    // skip: satVar -> value, drawn from the active trail.
    std::unordered_map<SatVar, bool> asserted;
    asserted.reserve(state_.trail.size() +
                     interfaceEqualities_.size() + interfaceDisequalities_.size());
    for (const auto& a : state_.trail) asserted[a.lit.var] = a.lit.sign;
    // IFACE_LIFECYCLE keeps interface (dis)equalities OFF state_.trail, so their
    // reason literals — genuinely assigned-true by the SAT core and held here
    // until backtrack prunes them — are invisible to the firewall above. That
    // false negative drops every array read-value form-pin whose justifying
    // bound is an interface equality (the cs_* wall: [LINPROP-drop] reasons U).
    // The reason literal of an entry currently IN interfaceEqualities_/
    // interfaceDisequalities_ is a currently-true fact (assertInterfaceEquality
    // is only called on an assigned atom, and onBacktrack removes entries whose
    // level was popped), so admitting it as true is SOUND — and the entailment
    // clause (¬reasons ∨ impliedAtom) it unblocks is a global theory tautology
    // regardless. Gated XOLVER_NIA_IFACE_PROP (default-OFF) for A/B + safety.
    static const bool ifaceProp = [] {
        return xolver::env::flag("XOLVER_NIA_IFACE_PROP");
    }();
    if (ifaceProp) {
        for (const auto& ie : interfaceEqualities_)
            asserted.emplace(ie.reason.var, ie.reason.sign);
        for (const auto& id : interfaceDisequalities_)
            asserted.emplace(id.reason.var, id.reason.sign);
    }
    auto isAssigned = [&](SatVar v) { return asserted.find(v) != asserted.end(); };
    auto litIsTrue = [&](SatLit l) {
        auto it = asserted.find(l.var);
        return it != asserted.end() && it->second == l.sign;
    };

    size_t entBefore = entailmentProps_.size();
    std::optional<TheoryConflict> conflict;
    linDecider_->collectLinearProp(
        registry_, *kernel_, normalized_, isAssigned, litIsTrue,
        &conflict, &entailmentProps_, &entailmentEmittedKeys_,
        /*maxEmit=*/256);

    static const bool diag = xolver::env::diag("XOLVER_NIA_LINPROP_DIAG");
    if (diag) {
        std::fprintf(stderr,
            "[LINPROP] fire active=%zu normalized=%zu effort=%d conflict=%s ent+=%zu (total=%zu)\n",
            active_.size(), normalized_.size(), (int)effort,
            conflict ? "yes" : "no",
            entailmentProps_.size() - entBefore, entailmentProps_.size());
        std::fflush(stderr);
    }

    if (conflict) return TheoryCheckResult::mkConflict(std::move(*conflict));
    return std::nullopt;   // pure producer otherwise — let the pipeline continue
}

std::optional<TheoryCheckResult> NiaSolver::stageNormalize(TheoryLemmaStorage&, TheoryEffort) {
    // HYB-1 DIAG hook (XOLVER_NIA_VAR_PARTITION_DIAG=1) — once per solve.
    // Placed at the TOP of stageNormalize so both the normCache fast-path
    // and the full-normalize path are exercised. Fires after normalized_
    // has been populated (i.e., after the cache update below). Cheap.
    auto emitPartitionDiag = [this]() {
        static const bool partDiag = xolver::env::diag("XOLVER_NIA_VAR_PARTITION_DIAG");
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

std::optional<TheoryCheckResult> NiaSolver::stageDispatchCacheLookup(TheoryLemmaStorage&, TheoryEffort) {
    static const bool dcEnabled = [] {
        return xolver::env::flag("XOLVER_NIA_DISPATCH_CACHE");
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
        return xolver::env::flag("XOLVER_NIA_DISPATCH_CACHE");
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

} // namespace xolver
