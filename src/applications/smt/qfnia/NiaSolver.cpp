#include "base/RuntimeConfig.h"
#include "applications/smt/qfnia/NiaSolver.h"
#include <algorithm>
#include "search/dl/DifferenceGraph.h"
#include "search/dl/BellmanFord.h"
#include "search/arith/Reasoner.h"
#include <random>
#include "search/nia/search/NiaLinearizationAdapter.h"
#include "search/nia/search/NiaIcpAdapter.h"
#include "search/icp/IcpTypes.h"
#include "search/nra/core/CdcacCore.h"
#include "search/nra/core/CdcacConstraint.h"
#include "search/nra/engine/ReasonManager.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "search/nra/backend/LibpolyBackend.h"
#include "search/nia/farkas/LeafFarkasLia.h"
#include "search/nra/reasoners/NlaCutsRunner.h"           // Stage 3 Phase C-3
#include "algebra/poly/RationalPolynomial.h"          // Stage 3 Phase C-3
#endif
#include "algebra/linear/LinearExpr.h"
#include "applications/smt/qfnia/NiaLinearDecider.h"  // embedded bounded LIA search (nia.linear-decide)
#include "search/linearizer/NonlinearTermAbstraction.h"
#include "algebra/linear/LinearConstraintNormalizer.h"
#include "contracts/LogicFeatureDetector.h"
#include "search/presolve/Presolve.h"
#include "search/candidate/CompleteFiniteDomainEnumerator.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "evidence/ArithModelValidator.h"
#include "base/EnvParam.h"
#include <functional>
#include <set>
#include "search/nia/farkas/FarkasOrDetector.h"
#include "search/nia/farkas/FarkasOrSolver.h"
#include "search/nia/farkas/FarkasOrModelAssembler.h"
#include "base/MpqUtils.h"
#include <chrono>
#include <iostream>

namespace xolver {
void NiaSolver::setNativeTerms(const NativeTerms* ir) {
    nativeTerms_ = ir;
    bbArrayGate_ = -1;  // recompute array-presence for the new IR (bit-blast gate)
    // Farkas-Or Phase 0: env-gated structural dump. Bypasses std::cerr
    // (which xolver-cli silently consumes); writes to the file named by
    // XOLVER_NIA_FARKAS_DUMP_FILE if set, else /tmp/farkas_dump.
    if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NIA_FARKAS_DUMP") && ir != nullptr) {
        const auto path = xolver::config::read<xolver::config::ReadKind::Path>("XOLVER_NIA_FARKAS_DUMP_FILE", "/tmp/farkas_dump");
        FILE* f = std::fopen(path.c_str(), "a");
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
            ReasonerSchedule::CandidateModel));
    };
    add("nia.pending",        &NiaSolver::stagePending);
    add("nia.normalize",      &NiaSolver::stageNormalize);
    // Bit-blast can examine the active constraints at partial and full effort.
    add("nia.bit-blast-early", &NiaSolver::stageBitBlastEarly);
    // Complete-candidate linear integer decision. The stage checks that every
    // normalized constraint is linear, validates any integer witness exactly,
    // and otherwise leaves the obligation to the remaining NIA stages.
    addFull("nia.linear-decide", &NiaSolver::stageLinearDecide);
    add("nia.presolve", &NiaSolver::stagePresolveFixpoint);
    // Full-effort shape cuts derived from explained single-variable bounds.
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
    // Search growing integer boxes before bit-blast. Candidates must satisfy
    // the original formula; exhausted boxes leave the remaining search open.
    addFull("nia.escalating-bounded", &NiaSolver::stageEscalatingBounded);
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
    // Farkas-Or model constructor (user 2026-06-02). For disjunctive
    // Farkas-certificate-synthesis problems (VeryMax/Stroeder), build
    // a structural CSP over (B, choice, CT), search via GAC backtrack,
    // assemble candidate model, validate against original NativeTerms via
    // ArithModelValidator. Returns SAT on validation pass; never UNSAT.
    // Standard+Full so it can fire BEFORE the expensive LS / BB stages
    // that the SAT-layer's theory checks usually exhaust.
    // Standard+Full. cb_propagate now handles Unknown (mirrors
    // cb_check_found_model), so the streak-3 Unknown bail terminates
    // SAT and lets Cap. 10 promote the validated model.
    add("nia.farkas-or", &NiaSolver::stageFarkasOr);
    add("nia.pending-lemma",  &NiaSolver::stagePendingLemma);
    add("nia.branch",         &NiaSolver::stageBranch);

}

void NiaSolver::onReset() {
    // Base clears state_.trail + its pending slot; NIA clears its own
    // polynomial stack, active literal set, level-tagged pendings, and
    // combination state.
    active_.clear();
    trail_.clear();
    normalized_.clear();
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
}

void NiaSolver::assertLit(const TheoryAtomRecord& atom, bool value,
                          int level, SatLit assertedLit) {
    auto r = activeSet_.insert(assertedLit);
    if (r == ActiveLiteralSet::InsertResult::Duplicate) {
        return;
    }
    if (r == ActiveLiteralSet::InsertResult::OppositePolarity) {
        const bool oppDiag = xolver::config::read<xolver::config::ReadKind::Presence>("NIA_OPP_DIAG");
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
    // Roll back normal atoms in level order. Interface constraints have their
    // own level-tagged storage and are pruned below.
    while (!trail_.empty() && trail_.back().level > level) {
        active_.resize(trail_.back().activeSizeBefore);
        trail_.pop_back();
    }
    activeSet_.rebuildFromActive(active_, [](const auto& c) { return c.reason; });
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
    bool fullReset = level == 0;
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


} // namespace xolver
