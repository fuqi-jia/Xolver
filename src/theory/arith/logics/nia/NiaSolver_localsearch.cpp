#include "theory/arith/logics/nia/NiaSolver.h"
#include "theory/arith/logics/nia/NiaSolverDetail.h"  // collectVars / dispatch-signature helpers (shared across split TUs)
#include <algorithm>
#include "theory/arith/logics/dl/DifferenceGraph.h"
#include "theory/arith/logics/dl/BellmanFord.h"
#include "theory/arith/logics/nia/preprocess/VariablePartition.h"
#include "theory/arith/Reasoner.h"
#include <random>
#include "theory/arith/logics/nia/search/NiaLinearizationAdapter.h"
#include "theory/arith/logics/nia/search/NiaIcpAdapter.h"
#include "theory/arith/kernel/icp/IcpTypes.h"
#include "theory/arith/logics/nra/core/CdcacCore.h"
#include "theory/arith/logics/nra/core/CdcacConstraint.h"
#include "theory/arith/logics/nra/engine/ReasonManager.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/logics/nra/backend/LibpolyBackend.h"
#include "theory/arith/logics/nia/farkas/LeafFarkasLia.h"
#include "theory/arith/logics/nra/reasoners/NlaCutsRunner.h"           // Stage 3 Phase C-3
#include "theory/arith/kernel/poly/RationalPolynomial.h"          // Stage 3 Phase C-3
#endif
#include "theory/arith/kernel/linear/LinearExpr.h"
#include "theory/arith/logics/nia/search/NiaLinearDecider.h"  // embedded complete-LIA (nia.linear-decide)
#include "theory/arith/logics/nia/reasoners/OmegaTest.h"        // nia.omega: sound linear-integer UNSAT
#include "theory/arith/logics/nia/reasoners/SmallPrimeModular.h" // nia.small-prime-modular: GF(p) schedule
#include "theory/arith/logics/nia/reasoners/IntBoundProp.h"      // nia.int-bound-prop: integer interval refutation
#include "theory/arith/kernel/linearizer/NonlinearTermAbstraction.h"
#include "theory/arith/kernel/linear/LinearConstraintNormalizer.h"
#include "theory/core/LogicFeatureDetector.h"
#include "theory/arith/kernel/presolve/Presolve.h"
#include "theory/arith/kernel/search/CompleteFiniteDomainEnumerator.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "proof/ArithModelValidator.h"
#include "util/EnvParam.h"
#include <functional>
#include <set>
#include "theory/arith/logics/nia/farkas/FarkasOrDetector.h"
#include "theory/arith/logics/nia/farkas/FarkasOrSolver.h"
#include "theory/arith/logics/nia/farkas/FarkasOrModelAssembler.h"
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

std::optional<TheoryCheckResult> NiaSolver::stageLocalSearch(TheoryLemmaStorage&, TheoryEffort) {
    // HYB-X partition-hint wire-up (default-OFF).
    {
        static const bool partHint = xolver::env::diag("XOLVER_NIA_LS_PARTITION_HINT");
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
        return xolver::env::flag("XOLVER_NIA_LS_BOOL_EXTEND");
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
        return xolver::env::flag("XOLVER_NIA_HYB_BB_LS");
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

// HYB-2 (post-Smart-LS). For ITS-like partitions (|B| >= |U|), LS
// has done the U-search and recorded per-var bounds. Pin U vars at
// the midpoint of their LS-visited range via DomainStore singletons,
// then run BitBlast on the residual (which now has only B-free vars,
// plus the pinned-U linear influence factored in). Validate against
// the original NIA formula.
std::optional<TheoryCheckResult> NiaSolver::stageHybridLsBb(TheoryLemmaStorage&, TheoryEffort) {
    static const bool enabled = [] {
        return xolver::env::flag("XOLVER_NIA_HYB_LS_BB");
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
        return xolver::env::flag("XOLVER_NIA_LS_EARLY");
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
        static const bool partHint = xolver::env::diag("XOLVER_NIA_LS_PARTITION_HINT");
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

} // namespace xolver
