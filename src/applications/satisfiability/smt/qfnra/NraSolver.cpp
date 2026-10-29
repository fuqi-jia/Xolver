#include "base/RuntimeConfig.h"
#include "applications/satisfiability/smt/qfnra/NraSolver.h"
#include "base/EnvParam.h"
#include "base/SolveClock.h"
#include <chrono>
#include "search/arith/Reasoner.h"
#include "algebra/linear/LinearExpr.h"
#include "search/presolve/Presolve.h"
#include "base/RealValue.h"                                // validated rational witness model
#include "search/nra/StructuralIntegerProbe.h"
#include "search/nra/NraSquareSolver.h"                   // algebraic square-cascade
#include "search/nra/reasoners/NraLocalSearch.h"
#include "search/nra/core/HybridPartitionStats.h"     // Task NRA-HYB Step 1 partition stats
#include "search/nra/simplex/CertifiedSimplexFacts.h"   // OSF-CDCAC P1
#include "search/nra/simplex/NraLinearExtractor.h"      // §4.2 classifyConstraints
#include "search/nra/simplex/SimplexTableauFacts.h"     // §4.2 linearSubsetUnsat
#include "search/icp/IcpEngineQ.h"
#include "search/icp/ContractorFactoryQ.h"
#include "search/icp/IcpTypes.h"
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

NraSolver::NraSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)),
      converter_(std::make_unique<PolynomialConverter>(*kernel_)),
      engine_(kernel_.get()) {
    cdcacMaxVars_ = xolver::config::read<xolver::config::ReadKind::Int>("XOLVER_NRA_CDCAC_MAX_VARS", 0);
    cdcacMaxDeg_  = xolver::config::read<xolver::config::ReadKind::Int>("XOLVER_NRA_CDCAC_MAX_DEGREE", 0);
    // Phase 2 reasoner pipeline: presolve fixpoint, then CDCAC.
    // NRA-MGC-PROFILE diagnostic: env-gated per-stage wall-time accounting.
    // Set XOLVER_NRA_STAGE_TIMING=1 for per-stage cumulative on exit.
    // Set XOLVER_NRA_STAGE_TRACE=1 for real-time per-call logging (slower).
    auto stageWrap = [this](const char* name, auto fn) {
        return [this, name, fn](TheoryLemmaStorage& db, TheoryEffort e)
                -> std::optional<TheoryCheckResult> {
            const bool timing = xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NRA_STAGE_TIMING");
            const bool trace = xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NRA_STAGE_TRACE");
            // File trace (XOLVER_NRA_STAGE_TRACE_FILE=path): the CLI runs the solve
            // on a worker thread whose stderr is suppressed AND the destructor
            // summary never surfaces on a timeout — so neither STAGE_TIMING nor
            // STAGE_TRACE is observable for the slow/TO cases that matter. A
            // per-call file append (flushed) survives both suppression and SIGKILL,
            // making upstream-stage profiling of TO'd QF_NRA cases possible.
            const auto traceFile = xolver::config::read<xolver::config::ReadKind::Path>("XOLVER_NRA_STAGE_TRACE_FILE");
            if (!timing && !trace && traceFile.empty()) return fn(db, e);
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
            if (!traceFile.empty()) {
                std::FILE* f = std::fopen(traceFile.c_str(), "a");
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

    // Refute affine relations between monomial values before substitutions or
    // projection can expand them. Feasibility leaves the nonlinear obligation.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.linear-relaxation",
        stageWrap("linear-relaxation",
                  [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageLinearRelaxation(db, e); })));
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.presolve",
        stageWrap("presolve", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stagePresolve(db, e); })));
    // Step 2.1 GLOBAL box-consistency refutation, EARLY (right after presolve, before
    // the covering engines): decides bound-contradiction families (hong) in ~ms,
    // short-circuiting the covering-tree blowup that stageCac would otherwise spend
    // 10s+ on. Sound (interval over-approximation). Default-on, no flag/budget.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.box-refute",
        stageWrap("box-refute", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageBoxRefute(db, e); })));
    // Local search constructs complete witnesses, so it shares the candidate
    // scheduling contract with CAC instead of consuming a one-shot attempt on
    // the first partial assignment.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.partial-linear-model",
        stageWrap("partial-linear-model", [this](TheoryLemmaStorage& db, TheoryEffort e) {
            return stagePartialLinearModel(db, e);
        }), ReasonerSchedule::CandidateModel));
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.local-search",
        stageWrap("local-search", [this](TheoryLemmaStorage& db, TheoryEffort e) {
            return stageLocalSearch(db, e);
        }), ReasonerSchedule::CandidateModel));
    // Positive-orthant sign-definiteness refutation after presolve.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.sign-refute",
        stageWrap("sign-refute", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageSignRefute(db, e); })));
    // Exact-validated equality-cascade candidates before covering search.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.eq-cascade",
        stageWrap("eq-cascade", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCascade(db, e); }),
        ReasonerSchedule::CandidateModel));
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.square-cascade",
        stageWrap("square-cascade", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageSquareCascade(db, e); }),
        ReasonerSchedule::CandidateModel));
    // Subtropical candidate search before full CAD; runs at Full effort.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.subtropical",
        stageWrap("subtropical", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageSubtropical(db, e); })));
    // Covering/projection can perform unbounded algebraic work. Run them only
    // on a complete Boolean candidate, after propagation has had a chance to
    // reject it. The Full check still requires a verdict from these backends;
    // skipping them during propagation never accepts a model.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.cac",
        stageWrap("cac", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCac(db, e); }),
        ReasonerSchedule::CandidateModel));
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.cdcac",
        stageWrap("cdcac", [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCdcac(db, e); }),
        ReasonerSchedule::CandidateModel));


}

// Out-of-line destructor owns the incomplete libpoly backend type.
NraSolver::~NraSolver() {
    if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NRA_STAGE_TIMING") && !stageTimingUs_.empty()) {
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

void NraSolver::onPush() {
    scopeStack_.push_back({activeLits_.size(), trail_.size(),
                           interfaceEqualities_.size(), interfaceDisequalities_.size()});
    engine_.push();
}

void NraSolver::onPop(uint32_t n) {
    for (uint32_t i = 0; i < n && !scopeStack_.empty(); ++i) {
        const auto snapshot = scopeStack_.back();
        scopeStack_.pop_back();
        activeLits_.resize(snapshot.activeSize);
        trail_.resize(snapshot.trailSize);
        interfaceEqualities_.resize(snapshot.equalitySize);
        interfaceDisequalities_.resize(snapshot.disequalitySize);
    }
    activeSet_.rebuildFromActive(activeLits_, [](const auto& lit) { return lit; });
    presolveConstraints_.resize(activeLits_.size());
    invalidateModel();
    engine_.pop(n);
}

void NraSolver::onReset() {
    engine_.reset();
    activeLits_.clear();
    trail_.clear();
    presolveConstraints_.clear();
    scopeStack_.clear();
    activeSet_.reset();
    interfaceEqualities_.clear();
    interfaceDisequalities_.clear();
    invalidateModel();
    lsSpentMs_ = 0;
    lsLastConstraints_.clear();
    lsCachedCandidate_.reset();
    hybStatsLastDumpedSize_ = static_cast<size_t>(-1);
    cacBackend_.reset();   // Release the cylindrical-covering backend.
}

void NraSolver::invalidateModel() {
    satFastModel_.reset();
    satCacAlgModel_.reset();
}

TheoryCheckResult NraSolver::check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    // A routing error must never erase prior constraints or reach a SAT stage.
    for (const auto& c : presolveConstraints_)
        if (c.poly == NullPoly)
            return TheoryCheckResult::unknown("nra-unsupported-atom-payload");
    if (config::read<config::ReadKind::Presence>("XOLVER_NRA_HYB_PARTITION_STATS") &&
        presolveConstraints_.size() != hybStatsLastDumpedSize_) {
        std::vector<PolyId> activePolys;
        for (const auto& c : presolveConstraints_) activePolys.push_back(c.poly);
        maybeDumpPartitionReport(computePartition(activePolys, *kernel_));
        hybStatsLastDumpedSize_ = presolveConstraints_.size();
    }
    return ArithSolverBase::check(lemmaDb, effort);
}

bool NraSolver::validateRationalCandidate(
    std::unordered_map<VarId, mpq_class>& candidate) const {
    std::unordered_map<std::string, mpq_class> values;
    for (const auto& [v, q] : candidate) values.emplace(kernel_->varName(v), q);
    auto holds = [&](PolyId poly, Relation rel) {
        if (poly == NullPoly) return false;
        // Missing variables are explicitly completed in the exported witness,
        // using the same value for every constraint in this candidate.
        for (const auto& name : kernel_->variables(poly)) {
            if (values.emplace(name, mpq_class(0)).second)
                candidate.emplace(kernel_->getOrCreateVar(name), mpq_class(0));
        }
        const int sign = kernel_->sgn(poly, values);
        return relationHolds(sign < 0 ? Sign::Neg : sign > 0 ? Sign::Pos : Sign::Zero, rel);
    };
    for (const auto& c : presolveConstraints_)
        if (!holds(c.poly, c.rel)) return false;
    for (const auto& c : interfaceEqualities_)
        if (!holds(c.poly, Relation::Eq)) return false;
    for (const auto& c : interfaceDisequalities_)
        if (!holds(c.poly, Relation::Neq)) return false;
    return true;
}

std::optional<TheoryCheckResult> NraSolver::stageLocalSearch(
    TheoryLemmaStorage&, TheoryEffort) {
    if (lsCachedCandidate_) {
        if (validateRationalCandidate(*lsCachedCandidate_)) {
            satFastModel_ = *lsCachedCandidate_;
            return TheoryCheckResult::consistent();
        }
        lsCachedCandidate_.reset();
    }

    std::vector<NraLocalSearch::Constraint> constraints;
    for (const auto& c : presolveConstraints_) constraints.push_back({c.poly, c.rel, c.reason});
    for (const auto& c : interfaceEqualities_) constraints.push_back({c.poly, Relation::Eq, c.reason});
    for (const auto& c : interfaceDisequalities_) constraints.push_back({c.poly, Relation::Neq, c.reason});
    if (constraints.empty()) return std::nullopt;

    std::vector<std::pair<PolyId, Relation>> key;
    std::set<VarId> varSet;
    for (const auto& c : constraints) {
        if (c.poly == NullPoly) return std::nullopt;
        const auto terms = kernel_->terms(c.poly);
        if (!terms) return std::nullopt;
        key.emplace_back(c.poly, c.rel);
        for (const auto& t : *terms)
            for (const auto& [v, exponent] : t.powers) varSet.insert(v);
    }
    std::sort(key.begin(), key.end());
    key.erase(std::unique(key.begin(), key.end()), key.end());
    if (varSet.empty() || key == lsLastConstraints_) return std::nullopt;

    const long allocation = wall::scaledBudgetMs(
        config::read<config::ReadKind::Long>("XOLVER_NRA_LS_BUDGET_MS", 250), 1, 10);
    if (allocation > 0 && lsSpentMs_ >= allocation) return std::nullopt;
    lsLastConstraints_ = std::move(key);
    NraLocalSearch search(*kernel_);
    search.setBudgetMs(allocation > 0 ? allocation - lsSpentMs_ : allocation);
    search.setMaxRounds(static_cast<int>(wall::scaledCount(
        config::read<config::ReadKind::Int>("XOLVER_NRA_LS_MAX_ROUNDS", 3000), 6000, 256)));
    const auto start = std::chrono::steady_clock::now();
    auto candidate = search.tryFindModel(constraints, {varSet.begin(), varSet.end()});
    // Charge partial milliseconds too: repeated tiny attempts still consume
    // the query allocation, rather than resetting a budget at each SAT callback.
    const auto elapsed = std::chrono::steady_clock::now() - start;
    lsSpentMs_ += std::chrono::duration_cast<std::chrono::milliseconds>(elapsed).count() + 1;
    if (candidate && validateRationalCandidate(*candidate)) {
        lsCachedCandidate_ = *candidate;
        satFastModel_ = std::move(*candidate);
        return TheoryCheckResult::consistent();
    }
    return std::nullopt;
}

void NraSolver::assertLit(const TheoryAtomRecord& atom, bool value,
                          int level, SatLit reason) {
    // Facade-level dedup: same polarity already active → ignore.
    // Opposite polarity is left to the engine's defense-in-depth check.
    if (activeSet_.contains(reason)) {
        return;
    }
    activeSet_.insert(reason);
    invalidateModel();

    size_t oldSize = activeLits_.size();
    activeLits_.push_back(reason);
    trail_.push_back({level, oldSize});
    const auto* payload = std::get_if<PolynomialAtomPayload>(&atom.payload);
    if (!payload) {
        // Payload mismatch is an internal routing error, NOT a theory conflict.
        // Engine will see this as unsupported and return Unknown.
        presolveConstraints_.push_back({NullPoly, Relation::Eq, reason});  // keep aligned
        return;
    }

    // Algebraic RHS is not representable in the rational polynomial kernel;
    // it never arises from rational inputs. Treat as unsupported → Unknown.
    auto rhsQ = payload->rhs.tryAsRational();
    if (!rhsQ) {
        presolveConstraints_.push_back({NullPoly, Relation::Eq, reason});  // keep aligned
        return;
    }

    Relation rel = value ? payload->rel : negateRelation(payload->rel);
    // Presolve sees the constraint in `p rel 0` form (subtract rhs if present).
    PolyId diff = payload->poly;
    if (*rhsQ != 0) diff = kernel_->sub(payload->poly, kernel_->mkConst(*rhsQ));
    presolveConstraints_.push_back({diff, rel, reason});
    engine_.assertConstraint(diff, rel, reason, level);
}

void NraSolver::onBacktrack(int level) {
    const size_t activeBefore = activeLits_.size();
    const size_t interfaceBefore = interfaceEqualities_.size() + interfaceDisequalities_.size();
    while (!trail_.empty() && trail_.back().level > level) {
        activeLits_.resize(trail_.back().activeSizeBefore);
        trail_.pop_back();
    }
    activeSet_.rebuildFromActive(activeLits_, [](const auto& lit) { return lit; });
    presolveConstraints_.resize(activeLits_.size());
    engine_.backtrack(level);
    auto ieIt = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceEqualities_.erase(ieIt, interfaceEqualities_.end());
    auto idIt = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceDisequalities_.erase(idIt, interfaceDisequalities_.end());
    // A no-op backtrack can follow SAT; preserve that model. Actual changes
    // include interface-only backtracking as well as ordinary literals.
    if (activeBefore != activeLits_.size() ||
        interfaceBefore != interfaceEqualities_.size() + interfaceDisequalities_.size())
        invalidateModel();
}


TheoryCheckResult NraSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {
    if (!sharedTermRegistry_ || !nativeTerms_ || !converter_)
        return TheoryCheckResult::unknown("nra-interface-registry-unavailable");
    const auto* stA = sharedTermRegistry_->get(a);
    const auto* stB = sharedTermRegistry_->get(b);
    if (!stA || !stB) return TheoryCheckResult::unknown("nra-interface-term-unavailable");

    auto cc = converter_->convertConstraint(stA->nativeExpr, stB->nativeExpr,
                                            Relation::Eq, *nativeTerms_);
    if (cc.status == PolyConstraintStatus::Tautology)
        return TheoryCheckResult::consistent();
    if (cc.status == PolyConstraintStatus::Conflict)
        return TheoryCheckResult::mkConflict(TheoryConflict{{reason}});
    if (!cc.isConstraint())
        return TheoryCheckResult::unknown("nra-interface-nonpolynomial");

    invalidateModel();
    engine_.assertConstraint(cc.diff, Relation::Eq, reason, level);
    interfaceEqualities_.push_back({a, b, reason, level, cc.diff});
    return TheoryCheckResult::consistent();
}

TheoryCheckResult NraSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {
    if (!sharedTermRegistry_ || !nativeTerms_ || !converter_)
        return TheoryCheckResult::unknown("nra-interface-registry-unavailable");
    const auto* stA = sharedTermRegistry_->get(a);
    const auto* stB = sharedTermRegistry_->get(b);
    if (!stA || !stB) return TheoryCheckResult::unknown("nra-interface-term-unavailable");

    auto cc = converter_->convertConstraint(stA->nativeExpr, stB->nativeExpr,
                                            Relation::Neq, *nativeTerms_);
    if (cc.status == PolyConstraintStatus::Tautology)
        return TheoryCheckResult::consistent();
    if (cc.status == PolyConstraintStatus::Conflict)
        return TheoryCheckResult::mkConflict(TheoryConflict{{reason}});
    if (!cc.isConstraint())
        return TheoryCheckResult::unknown("nra-interface-nonpolynomial");

    invalidateModel();
    engine_.assertConstraint(cc.diff, Relation::Neq, reason, level);
    interfaceDisequalities_.push_back({a, b, reason, level, cc.diff});
    return TheoryCheckResult::consistent();
}

std::optional<TheorySolver::TheoryModel> NraSolver::getModel() const {
    // If a rational candidate search produced a validated witness
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
