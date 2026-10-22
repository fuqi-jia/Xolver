#include "base/RuntimeConfig.h"
#include "search/nia/NiaSolver.h"
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
#include "search/nia/search/NiaLinearDecider.h"  // embedded bounded LIA search (nia.linear-decide)
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
    // Interface (dis)equalities live off active_, so
    // an empty active_ may still carry combination obligations to solve.
    if (active_.empty() &&
        interfaceEqualities_.empty() && interfaceDisequalities_.empty())
        return TheoryCheckResult::consistent();
    return std::nullopt;
}

// NIA owns its linear atoms, including in array/UF combination. Replay the
// normalized active set into simplex and bounded integer search. Only an
// independently validated integer model establishes consistency. A root LP
// conflict carries the original asserted reasons; inconclusive search defers
// to the remaining NIA stages.
std::optional<TheoryCheckResult> NiaSolver::stageLinearDecide(
    TheoryLemmaStorage&, TheoryEffort effort) {
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

    if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NIA_LINDECIDE_DIAG"))
        std::fprintf(stderr, "[LINDECIDE] stage fired: active=%zu normalized=%zu trail=%zu\n",
                     active_.size(), normalized_.size(), state_.trail.size());

    // Delegate to the embedded bounded LIA search decision (own TU). It returns either
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

std::optional<TheoryCheckResult> NiaSolver::stageNormalize(TheoryLemmaStorage&, TheoryEffort) {
    // Merge live interface constraints with normal atoms before normalization.
    const std::vector<ActiveNiaConstraint>* toNormalize = &active_;
    std::vector<ActiveNiaConstraint> merged;
    if (!(interfaceEqualities_.empty() && interfaceDisequalities_.empty())) {
        merged.reserve(active_.size() + interfaceEqualities_.size() +
                       interfaceDisequalities_.size());
        merged = active_;
        for (const auto& ie : interfaceEqualities_)
            if (ie.diff != NullPoly) merged.push_back({ie.diff, ie.rel, ie.reason});
        for (const auto& id : interfaceDisequalities_)
            if (id.diff != NullPoly) merged.push_back({id.diff, id.rel, id.reason});
        toNormalize = &merged;
    }
    normalized_ = normalizer_.normalize(*toNormalize);
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
    const long presolveBudgetMs =
        config::read<config::ReadKind::Long>("XOLVER_NIA_PRESOLVE_BUDGET_MS", 50);
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
