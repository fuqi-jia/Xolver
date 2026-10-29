#include "base/RuntimeConfig.h"
#include "applications/satisfiability/smt/qfnra/NraSolver.h"
#include "base/EnvParam.h"
#include "base/SolveClock.h"
#include <chrono>
#include "search/arith/Reasoner.h"
#include "algebra/linear/LinearExpr.h"
#include "search/presolve/Presolve.h"
#include "algebra/poly/RationalPolynomial.h"
#include "base/RealValue.h"                                // validated rational witness model
#include "search/nra/StructuralIntegerProbe.h"
#include "search/nra/NraSquareSolver.h"                   // algebraic square-cascade
#include "search/nra/core/HybridPartitionStats.h"     // Task NRA-HYB Step 1 partition stats
#include "search/nra/simplex/CertifiedSimplexFacts.h"   // OSF-CDCAC P1
#include "search/nra/simplex/NraLinearExtractor.h"      // §4.2 classifyConstraints
#include "search/nra/simplex/SimplexTableauFacts.h"     // §4.2 linearSubsetUnsat
#include "search/icp/IcpEngineQ.h"
#include "search/icp/ContractorFactoryQ.h"
#include "search/icp/IcpTypes.h"
#include "search/nra/cac/CacEngine.h"                    // conflict-driven coverings
#include "search/nra/core/CdcacCommon.h"                 // #63 relationHolds() for rational-fallback
#include "search/nra/core/CdcacCore.h"
#include "search/nra/core/CdcacConstraint.h"
#include "search/nra/engine/ReasonManager.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "search/nra/backend/LibpolyBackend.h"
#include "search/nra/reasoners/NlaCutsRunner.h"
#endif
#include <cstdlib>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <fstream>
#include <iostream>

namespace xolver {

// NOTE: This translation unit was split out of NraSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

// Conflict-driven cylindrical covering precedes the Collins backend.
std::optional<TheoryCheckResult> NraSolver::stageCac(TheoryLemmaStorage& /*lemmaDb*/,
                                                     TheoryEffort effort) {
    if (!xolver::config::read<xolver::config::ReadKind::Path>("XOLVER_NRA_TOWER_DIAG").empty())
        std::cerr << "[STAGE-CAC] entry effort=" << static_cast<int>(effort) << std::endl;
    // Candidate-model scheduling is owned by the reasoner pipeline. There is
    // no runtime switch that reintroduces unrestricted CAD in propagation.
    // Interface constraints are owned by the combination backend.
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
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
    // ====================================================================
    // Shape cuts derived from explained interval bounds.
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
    if (cacCons.empty() || varSet.empty()) return std::nullopt;
    std::vector<VarId> varOrder(varSet.begin(), varSet.end());  // sorted (std::set)

    if (!cacBackend_) cacBackend_ = std::make_unique<LibpolyBackend>(kernel_.get());
    // Give CAC a bounded share before the complete projection fallback.
    const long cacDeadlineMs =
        config::read<config::ReadKind::Long>("XOLVER_NRA_CAC_DEADLINE_MS", 2000);
    CacEngine::Config cfg;
    // Scale CAC's deadline to ~1/4 of the wall-clock remaining when
    // XOLVER_WALLCLOCK_SCALE is on (else == cacDeadlineMs). Lets CAC keep
    // working when the competition timeout leaves time, instead of yielding
    // to Collins at a flat 2s and then idling.
    cfg.deadlineMillis = wall::scaledBudgetMs(cacDeadlineMs, 1, 4);
    CacEngine eng(cacBackend_.get(), kernel_.get(), varOrder, std::move(cacCons), cfg);
    CacResult res = eng.solve();

    const bool diag = xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NRA_CAC_DIAG");
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
        // Use attributed covering reasons, with all active reasons as fallback.
        if (!res.unsatCore.empty()) {
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
        bool anyAlgebraic = false;
        for (size_t i = 0; i < res.model.values.size(); ++i) {
            if (!res.model.values[i].isRational()) { anyAlgebraic = true; break; }
        }
        if (anyAlgebraic) return std::nullopt;
        {
            std::unordered_map<VarId, mpq_class> rationalModel;
            for (size_t i = 0; i < res.model.values.size(); ++i)
                rationalModel.emplace(res.model.varOrder[i], res.model.values[i].rational);
            satFastModel_ = std::move(rationalModel);
        }
        return TheoryCheckResult::consistent();
    }
#endif
    return std::nullopt;  // Unknown / no libpoly ⇒ fall through to Collins
}

// Candidate-model fallback. May return Unknown on resource/fragment limits.
std::optional<TheoryCheckResult> NraSolver::stageCdcac(TheoryLemmaStorage& /*lemmaDb*/,
                                                       TheoryEffort /*effort*/) {
    if (!xolver::config::read<xolver::config::ReadKind::Path>("XOLVER_NRA_TOWER_DIAG").empty())
        std::cerr << "[STAGE-CDCAC] reached (engine_ will run core_->solve)" << std::endl;
    // libpoly hardening (XOLVER_NRA_CDCAC_MAX_VARS / _MAX_DEGREE, 0=disabled):
    // decline pathologically large systems where libpoly (CDCAC's CAD backend) can
    // blow up / OOM, returning unknown (SOUND — declining to decide is never a wrong
    // verdict) rather than risking a process-killing crash. A robustness guard; the
    // threshold is tuned on the benchmark set (E1). Default disabled ⇒ no corpus impact.
    if (cdcacMaxVars_ > 0 || cdcacMaxDeg_ > 0) {
        std::set<std::string> vars;
        int maxDeg = 0;
        for (const auto& c : presolveConstraints_) {
            if (c.poly == NullPoly) continue;
            for (const auto& v : kernel_->variables(c.poly)) {
                vars.insert(v);
                if (auto d = kernel_->degree(c.poly, v)) maxDeg = std::max(maxDeg, *d);
            }
        }
        if ((cdcacMaxVars_ > 0 && static_cast<int>(vars.size()) > cdcacMaxVars_) ||
            (cdcacMaxDeg_ > 0 && maxDeg > cdcacMaxDeg_)) {
            if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NRA_CDCAC_GUARD_DIAG"))
                std::fprintf(stderr, "[CDCAC-GUARD] declined: vars=%zu maxDeg=%d\n",
                             vars.size(), maxDeg);
            return TheoryCheckResult::unknown("cdcac-input-exceeds-libpoly-guard");
        }
    }
    return engine_.check();
}

} // namespace xolver
