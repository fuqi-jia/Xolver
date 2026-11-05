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
    std::vector<std::vector<SatLit>> activeReasons;
    std::vector<SignRefuteConstraint> boundSources;
    std::set<VarId> varSet;
    cacCons.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) return std::nullopt;          // non-polynomial ⇒ defer to Collins
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) return std::nullopt;
        for (VarId v : rp->variables()) varSet.insert(v);
        boundSources.push_back({*rp, c.rel, c.reason});
        cacCons.push_back({std::move(*rp), c.rel});
        activeReasons.push_back({c.reason});
    }
    // The covering core indexes constraints; each entry can depend on
    // several original bounds. Expand those explanations on conflict.
    const auto intervals = nlaCuts_->collectIntervals(boundSources);
    const auto cuts = nlaCuts_->runShapeCuts(intervals, /*maxPairs=*/0);
    for (const auto& cut : cuts) {
        if (cut.poly == NullPoly) continue;
        auto rp = RationalPolynomial::fromPolyId(cut.poly, *kernel_);
        if (!rp) continue;
        for (VarId v : rp->variables()) varSet.insert(v);
        cacCons.push_back({std::move(*rp), cut.rel});
        activeReasons.push_back(cut.reasons);
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
        auto include = [&](const std::vector<SatLit>& reasons) {
            for (const auto reason : reasons)
                if (std::find(conflict.clause.begin(), conflict.clause.end(), reason) == conflict.clause.end())
                    conflict.clause.push_back(reason);
        };
        const bool validCore = !res.unsatCore.empty() &&
            std::all_of(res.unsatCore.begin(), res.unsatCore.end(),
                [&](size_t index) { return index < activeReasons.size(); });
        if (validCore) for (const auto index : res.unsatCore) include(activeReasons[index]);
        if (!validCore || conflict.clause.empty())
            for (const auto& reasons : activeReasons) include(reasons);
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
