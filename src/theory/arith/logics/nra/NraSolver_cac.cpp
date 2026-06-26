#include "theory/arith/logics/nra/NraSolver.h"
#include "util/EnvParam.h"
#include "util/SolveClock.h"
#include <chrono>
#include "theory/arith/Reasoner.h"
#include "theory/arith/kernel/linear/LinearExpr.h"
#include "theory/arith/kernel/presolve/Presolve.h"
#include "theory/arith/kernel/poly/RationalPolynomial.h"
#include "util/RealValue.h"                                // XOLVER_NRA_SUBTROPICAL witness model
#include "theory/arith/logics/nra/NraLinearizationAdapter.h"     // XOLVER_NRA_LINEARIZE cut-feeder
#include "theory/arith/logics/nia/preprocess/NiaNormalizer.h"    // XOLVER_NRA_LINEARIZE: normalize nonlinear cstrs
#include "theory/arith/logics/nra/reasoners/SubtropicalSatFinder.h"  // XOLVER_NRA_SUBTROPICAL SAT-fast-path
#include "theory/arith/logics/nra/StructuralIntegerProbe.h"          // XOLVER_NRA_INT_PROBE
#include "theory/arith/logics/nra/NraSquareSolver.h"                   // algebraic square-cascade
#include "theory/arith/logics/nra/reasoners/NraLocalSearch.h"        // XOLVER_NRA_LOCALSEARCH Phase NRA-LS-A
#include "theory/arith/logics/nra/search/HybridPartitionStats.h"     // Task NRA-HYB Step 1 partition stats
#include "theory/arith/logics/nra/simplex/CertifiedSimplexFacts.h"   // OSF-CDCAC P1
#include "theory/arith/logics/nra/simplex/NraLinearExtractor.h"      // §4.2 classifyConstraints
#include "theory/arith/logics/nra/simplex/SimplexTableauFacts.h"     // §4.2 linearSubsetUnsat
#include "theory/arith/logics/nra/simplex/PolynomialIntervalPruner.h" // OSF-CDCAC P7
#include "theory/arith/kernel/icp/IcpEngineQ.h"                       // XOLVER_NRA_ICP rational ICP engine
#include "theory/arith/kernel/icp/ContractorFactoryQ.h"               // XOLVER_NRA_ICP factory
#include "theory/arith/kernel/icp/IcpTypes.h"                         // XOLVER_NRA_ICP IcpConstraint
#include "theory/arith/logics/nra/cac/CacEngine.h"                    // XOLVER_NRA_CAC conflict-driven coverings
#include "theory/arith/logics/nra/core/CdcacCommon.h"                 // #63 relationHolds() for rational-fallback
#include "theory/arith/kernel/refute/SignDefinitenessRefuter.h"       // XOLVER_NRA_SIGN_REFUTE
#include "theory/arith/logics/nra/core/CdcacCore.h"               // XOLVER_NRA_PREELIM reduced CDCAC
#include "theory/arith/logics/nra/core/CdcacConstraint.h"         // XOLVER_NRA_PREELIM
#include "theory/arith/logics/nra/engine/ReasonManager.h"         // XOLVER_NRA_PREELIM conflict reasons
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/logics/nra/backend/LibpolyBackend.h"       // XOLVER_NRA_PREELIM algebra backend
#include "theory/arith/logics/nra/nla/NlaCutsRunner.h"             // XOLVER_NRA_NLA_CUTS Phase C-2 hook
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

// XOLVER_NRA_CAC: conflict-driven single-cell CAC engine (the "real" CDCAC) as
// the primary NRA decision, run BEFORE the Collins buildClosure. A/B control for
// the Collins-vs-CAC differential; promotion to default is decided by that diff.
std::optional<TheoryCheckResult> NraSolver::stageCac(TheoryLemmaStorage& /*lemmaDb*/,
                                                     TheoryEffort effort) {
    if (xolver::env::diag("XOLVER_NRA_TOWER_DIAG"))
        std::cerr << "[STAGE-CAC] entry effort=" << static_cast<int>(effort)
                  << " enableCac=" << enableCac_ << std::endl;
    if (!enableCac_) return std::nullopt;
    // EFFORT SCHEDULE (validated by the Collins-vs-CAC A/B + endorsed design):
    //   Standard effort → cheap engines (Collins as cheap CAD, linearized checks);
    //   Full effort     → the heavy CAC/Lazard hard path (this stage), then Collins
    //                     as fallback on CAC-Unknown (stageCdcac runs at all efforts).
    // So in the hybrid CAC runs ONLY at Full: it gets first refusal on the hard
    // cases Collins times out on, while Collins disposes of the easy cases cheaply
    // at Standard — running the heavy CAC at every Standard propagation instead
    // STARVES the time budget (50/150 meti-tarski timeouts in the all-efforts A/B).
    // A fair head-to-head still needs CAC at all efforts (else Collins preempts it
    // at Standard and CAC never runs) — that is what XOLVER_NRA_CAC_ONLY enables
    // (CAC at every effort + Collins disabled): CAC-only=95 vs Collins-only=64,
    // 0-unsound, confirming CAC is the stronger engine on the hard path.
    // Two orthogonal differential flags (decoupled so the full schedule matrix
    // A-E is expressible): CAC_ALL_EFFORTS runs CAC at Standard+Full (else Full
    // only); CAC_NO_COLLINS (read in stageCdcac) disables the Collins fallback.
    // NRA-COLLINS-BUDGET fix (2026-06-02): CAC_ALL_EFFORTS source-default ON.
    // Empirical: paired test 10-case meti-tarski/sqrt sample shows 10 OK / 0 TO
    // @ 1s wall vs default's 9 OK / 1 TO @ 18s. NRA reg 151/151 unchanged.
    // The legacy comment about "50/150 meti-tarski timeouts" was stale; the
    // current binary handles CAC at Standard effort efficiently. Mulligan-0004c
    // bucket recovers (Collins hangs blocked CDCAC from reaching the case).
    // Env var preserved for opt-out: XOLVER_NRA_CAC_ALL_EFFORTS=0 disables.
    static const bool cacAllEfforts = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_ALL_EFFORTS");
        if (e && *e) return *e != '0';   // explicit opt-in/opt-out
        const char* o = std::getenv("XOLVER_NRA_CAC_ONLY");   // legacy alias
        if (o && *o && *o != '0') return true;
        return true;   // source default-ON
    }();
    if (!cacAllEfforts && effort != TheoryEffort::Full) return std::nullopt;
    // COMBINATION-AWARE CAC (XOLVER_NRA_CAC_COMBINATION, default OFF — the UFNRA
    // medal lane; pairs with EQNA who owns the N-O loop). When OFF, CAC stays
    // PURE-NRA: interface (dis)equalities live in engine_ (asserted via
    // assertInterfaceEquality), not presolveConstraints_, so a CAC verdict that
    // ignored them could be wrong → defer to Collins. When ON, we instead lift
    // the interface (dis)eqs into the CAC constraint set below (root/sign-
    // preserving real constraints poly(a)-poly(b) rel 0), so CAC decides under
    // them and its UNSAT conflict carries their reason lits (see below).
    static const bool cacCombination = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_COMBINATION");
        return e && *e && *e != '0';
    }();
    if (!cacCombination &&
        (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty()))
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
    // Combination: lift each N-O interface (dis)equality into a CAC constraint,
    // keeping its reason lit aligned in activeReasons (index ⇒ reason). The
    // conversion REUSES the exact path assertInterfaceEquality fed to engine_
    // (PolynomialConverter::convertConstraint → cc.diff rel 0). If a shared term
    // is not NRA-poly-expressible (UF app feeding a real var) → DEFER the whole
    // CAC run to Collins (sound floor: engine_ already has the interface
    // constraints). The unsatCore (origins) machinery then makes the combination
    // conflict include exactly the interface lits that participated.
    if (cacCombination) {
        auto liftIface = [&](const std::vector<InterfaceEq>& ifaces, Relation rel) -> bool {
            for (const auto& e : ifaces) {
                if (!sharedTermRegistry_ || !coreIr_ || !converter_) return false;
                const auto* stA = sharedTermRegistry_->get(e.a);
                const auto* stB = sharedTermRegistry_->get(e.b);
                if (!stA || !stB) return false;
                auto cc = converter_->convertConstraint(stA->coreExpr, stB->coreExpr, rel, *coreIr_);
                if (cc.status == PolyConstraintStatus::Tautology) continue;   // adds nothing
                if (cc.status == PolyConstraintStatus::Conflict) return false; // constant clash → defer (engine_ caught it at assert)
                if (!cc.isConstraint()) return false;                         // not poly-expressible → defer
                auto rp = RationalPolynomial::fromPolyId(cc.diff, *kernel_);
                if (!rp) return false;
                for (VarId v : rp->variables()) varSet.insert(v);
                cacCons.push_back({std::move(*rp), rel});
                activeReasons.push_back(e.reason);
            }
            return true;
        };
        if (!liftIface(interfaceEqualities_, Relation::Eq) ||
            !liftIface(interfaceDisequalities_, Relation::Neq))
            return std::nullopt;   // shared term not poly-expressible ⇒ sound defer to Collins
    }

    // ====================================================================
    // Phase C-2: NLA-cuts hook (XOLVER_NRA_NLA_CUTS, default-OFF).
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
    static const bool nlaCutsEnabled = [] {
        return xolver::env::flag("XOLVER_NRA_NLA_CUTS");
    }();
    if (nlaCutsEnabled) {
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
    }

    if (cacCons.empty() || varSet.empty()) return std::nullopt;
    std::vector<VarId> varOrder(varSet.begin(), varSet.end());  // sorted (std::set)

    // Track C round 4 #51: variable-order heuristic. Brown-McCallum-style
    // simplified: for each var compute (maxDeg, occCount) across cacCons; sort
    // varOrder ascending by (deg, occ) so low-info vars project out first
    // (outer), keeping high-degree vars as the lifting base (inner). Tiebreaker:
    // source VarId (stable, reproducible). Soundness: variable order does not
    // affect CDCAC completeness — it cannot introduce unsoundness, only shift
    // perf. Gated XOLVER_NRA_CAC_VAR_ORDER, default OFF.
    static const bool varOrderHeuristic = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_VAR_ORDER");
        return e && *e && *e != '0';
    }();
    if (varOrderHeuristic && varOrder.size() > 1) {
        std::unordered_map<VarId, std::pair<int, int>> scores;   // var -> (maxDeg, occCount)
        scores.reserve(varOrder.size());
        for (VarId v : varOrder) scores[v] = {0, 0};
        for (const auto& c : cacCons) {
            for (VarId v : c.poly.variables()) {
                auto it = scores.find(v);
                if (it == scores.end()) continue;
                const int d = c.poly.degree(v);
                if (d > it->second.first) it->second.first = d;
                ++it->second.second;
            }
        }
        // XOLVER_NRA_CAC_VAR_ORDER_DIR: "asc" (default, classic Collins —
        // low-degree first) or "desc" (high-degree first — matches z3-nlsat
        // decision heuristic; needed for SAT-sample sweep to hit structural
        // vars like vv3^9 at level 0 instead of being projected last).
        static const bool descOrder = [] {
            const char* e = std::getenv("XOLVER_NRA_CAC_VAR_ORDER_DESC");
            return e && *e && *e != '0';
        }();
        std::sort(varOrder.begin(), varOrder.end(), [&](VarId a, VarId b) {
            const auto& sa = scores[a];
            const auto& sb = scores[b];
            if (sa.first != sb.first) {
                return descOrder ? (sa.first > sb.first) : (sa.first < sb.first);
            }
            if (sa.second != sb.second) {
                return descOrder ? (sa.second > sb.second) : (sa.second < sb.second);
            }
            return a < b;   // stable tiebreaker on source VarId
        });
    }

    if (!cacBackend_) cacBackend_ = std::make_unique<LibpolyBackend>(kernel_.get());
    // Wall-clock deadline: in the HYBRID (Collins fallback present) bound CAC@Full
    // to a time-share so a hard covering YIELDS to Collins (Unknown→fallback)
    // rather than grinding to the global timeout and starving it. When CAC is the
    // SOLE engine (XOLVER_NRA_CAC_NO_COLLINS / _ONLY) leave it unbounded (0) and
    // rely on the external timeout. Override via XOLVER_NRA_CAC_DEADLINE_MS.
    static const bool soleEngine = [] {
        const char* n = std::getenv("XOLVER_NRA_CAC_NO_COLLINS");
        const char* o = std::getenv("XOLVER_NRA_CAC_ONLY");
        return (n && *n && *n != '0') || (o && *o && *o != '0');
    }();
    // hybrid default: 2s CAC@Full share (2s-beats-60s: a hard covering yields
    // fast to Collins instead of grinding); rest of 1200s is Collins.
    static const long cacDeadlineMs =
        env::paramLong("XOLVER_NRA_CAC_DEADLINE_MS", 2000);
    static const bool earlyInfeas = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_EARLY_INFEAS");
        return e && *e && *e != '0';
    }();
    static const bool pruneIntervals = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_PRUNE_INTERVALS");
        return e && *e && *e != '0';
    }();
    static const bool earlyInfeasSafe = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_EARLY_INFEAS_SAFE");
        return e && *e && *e != '0';
    }();
    const bool inloopPrune = true;  // promoted default-ON
    CacEngine::Config cfg;
    // Scale CAC's deadline to ~1/4 of the wall-clock remaining when
    // XOLVER_WALLCLOCK_SCALE is on (else == cacDeadlineMs). Lets CAC keep
    // working when the competition timeout leaves time, instead of yielding
    // to Collins at a flat 2s and then idling.
    cfg.deadlineMillis = soleEngine ? 0 : wall::scaledBudgetMs(cacDeadlineMs, 1, 4);
    cfg.earlyInfeas = earlyInfeas;
    cfg.pruneIntervals = pruneIntervals;
    cfg.earlyInfeasSafe = earlyInfeasSafe;
    cfg.inloopPrune = inloopPrune;
    // #63 Phase C2: keep a copy of cacCons for the rational-fallback validator.
    // (CacEngine std::move's the constraint vector below, leaving cacCons empty.)
    std::vector<CacConstraint> consCopy = cacCons;
    CacEngine eng(cacBackend_.get(), kernel_.get(), varOrder, std::move(cacCons), cfg);
    CacResult res = eng.solve();

    const bool diag = xolver::env::diag("XOLVER_NRA_CAC_DIAG");
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
        // CONFLICT MINIMIZATION (XOLVER_NRA_CAC_MIN_CONFLICT, default OFF): use
        // only the reason lits of the constraints that actually delineated the
        // covering (CacResult::unsatCore) instead of the whole asserted set.
        // The sub-conjunction over those constraints is itself UNSAT (the covering
        // proves it), so the learned lemma is sound and much tighter — less SAT-
        // core churn. unsatCore is a conservative superset of the minimal core;
        // an EMPTY core (could-not-attribute) falls back to all reasons (sound).
        // This is ALSO the mechanism the combination conflict will reuse to carry
        // the interface-(dis)eq lits that participated (see CAC.md / task P5).
        // PROMOTED default-ON (Feature B / lemma learning): the tight learned clause
        // (¬unsatCore) is sound because unsatCore over-attributes (conservative superset
        // of the minimal core), so the sub-conjunction the covering refuted is itself
        // UNSAT. A tighter clause = less SAT-core churn across the whole search — this is
        // the sound cross-search "lemma reuse", delegated to the SAT clause DB. Set
        // XOLVER_NRA_CAC_MIN_CONFLICT=0 to fall back to the whole asserted set.
        static const bool minConflict = [] {
            const char* e = std::getenv("XOLVER_NRA_CAC_MIN_CONFLICT");
            return !e || (e[0] != '0' && e[0] != 'f' && e[0] != 'F' && e[0] != 'n' && e[0] != 'N');
        }();
        if (minConflict && !res.unsatCore.empty()) {
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
        // COMBINATION (#43): a CAC SAT under interface constraints means NRA is
        // consistent with the asserted (dis)eqs. With XOLVER_NRA_CAC_COMB_SAT
        // ON, getDeducedSharedEqualities() emits the pairwise shared-term
        // equalities the model implies, so the combination loop can build the
        // arrangement directly. With it OFF (default), defer to Collins as
        // before (the v1 conservative path).
        static const bool combSatHere = [] {
            const char* e = std::getenv("XOLVER_NRA_CAC_COMB_SAT");
            return e && *e && *e != '0';
        }();
        if (!combSatHere && cacCombination &&
            (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty()))
            return std::nullopt;
        // Phase B (#55, XOLVER_NRA_CAC_SAT_ALGEBRAIC default OFF): accept
        // CAC SAT models with algebraic values. CAC's engine validated
        // allHold via exact signAt before returning SAT (existing invariant
        // 1); the model — rational or algebraic — is a genuine satisfier of
        // every constraint. Pre-#55 the algebraic case was deferred to
        // Collins, which timed out on the meti-tarski/sqrt cluster (4 of 5
        // sample cases had CAC verdict=sat repeatedly dropped here).
        static const bool acceptAlgebraic = [] {
            const char* e = std::getenv("XOLVER_NRA_CAC_SAT_ALGEBRAIC");
            return e && *e && *e != '0';
        }();
        bool anyAlgebraic = false;
        for (size_t i = 0; i < res.model.values.size(); ++i) {
            if (!res.model.values[i].isRational()) { anyAlgebraic = true; break; }
        }
        if (anyAlgebraic && !acceptAlgebraic) return std::nullopt;
        if (!anyAlgebraic) {
            std::unordered_map<VarId, mpq_class> rationalModel;
            for (size_t i = 0; i < res.model.values.size(); ++i)
                rationalModel.emplace(res.model.varOrder[i], res.model.values[i].rational);
            satFastModel_ = std::move(rationalModel);
        } else {
            // Algebraic channel: keep the full typed value (rational or
            // RealAlg) for getModel to surface to ArithModelValidator and
            // the printed-model channel.
            std::vector<std::pair<VarId, RealValue>> alg;
            alg.reserve(res.model.values.size());
            for (size_t i = 0; i < res.model.values.size(); ++i) {
                const auto& v = res.model.values[i];
                if (v.isRational()) {
                    alg.emplace_back(res.model.varOrder[i], RealValue::fromMpq(v.rational));
                } else {
                    // RealAlg → RealValue: mirror CdcacSolver::sampleValueToRealValue.
                    // The backend stores coefficients high-to-low; AlgebraicNumber
                    // wants low-to-high. Degenerate (no defining poly) → rational
                    // midpoint of the isolating interval (fallback).
                    RealValue rv;
                    if (cacBackend_ && v.root.definingPoly != NullUniPolyId) {
                        const auto& hiToLo = cacBackend_->getUni(v.root.definingPoly);
                        AlgebraicNumber an;
                        an.coefficients.assign(hiToLo.rbegin(), hiToLo.rend());
                        an.lower = v.root.lower;
                        an.upper = v.root.upper;
                        an.lowerOpen = true;
                        an.upperOpen = true;
                        rv = RealValue::fromAlgebraic(std::move(an));
                    } else {
                        const mpq_class mid = (v.root.lower + v.root.upper) / 2;
                        rv = RealValue::fromMpq(mid);
                    }
                    alg.emplace_back(res.model.varOrder[i], std::move(rv));
                }
            }
            satCacAlgModel_ = std::move(alg);
        }
        return TheoryCheckResult::consistent();
    }
    // #63 Phase C2 follow-on: when CAC bails on `leaf-atom-unsupported` with a
    // captured failing sample, attempt a rational-fallback retry. Replace each
    // algebraic coord with its isolating-interval midpoint, then EXACT-sign-
    // check every active CAC constraint at the rational sample. If ALL hold,
    // the rational sample is a genuine satisfier — invariant 1: this is an
    // exact-validated SAT, not a CAC-projected one. UNSAT verdicts from the
    // rational system are NEVER returned (could be false-UNSAT since rounding
    // algebraic to midpoint can miss the true satisfier); only sat is taken.
    // The cluster-wide diagnostic shows 100% of atan/CMOS timeouts and 96% of
    // exp timeouts hit this exact failure mode (see Phase C2 docs).
    static const bool rationalFallback = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_RATIONAL_FALLBACK");
        return e && *e && *e != '0';
    }();
    if (rationalFallback &&
        res.status == CacStatus::Unknown &&
        !res.unknownSample.varOrder.empty() &&
        res.unknownSample.varOrder.size() == res.unknownSample.values.size()) {

        // Build the set of candidate rational values for each var. For a rational
        // sample value, the single value. For an algebraic value (root in (lo, hi)),
        // probe at three offsets: lo + 1/4 * (hi-lo), 1/2 * (hi+lo), hi - 1/4 * (hi-lo)
        // — covering both sides of the algebraic root so a sign-flipping constraint
        // has a positive chance of being satisfied at one of the probes.
        const size_t N = res.unknownSample.varOrder.size();
        std::vector<std::vector<mpq_class>> candidates(N);
        for (size_t i = 0; i < N; ++i) {
            const auto& v = res.unknownSample.values[i];
            if (v.isRational()) {
                candidates[i].push_back(v.rational);
            } else {
                const mpq_class width = v.root.upper - v.root.lower;
                candidates[i].push_back(v.root.lower + width / 4);
                candidates[i].push_back(v.root.lower + width / 2);
                candidates[i].push_back(v.root.upper - width / 4);
            }
        }

        // Cap the cartesian product enumeration: at most 3^4 = 81 probes; for >4
        // algebraic vars use midpoints only (1 probe).
        size_t totalProbes = 1;
        for (const auto& c : candidates) totalProbes *= c.size();
        if (totalProbes > 81) {
            for (size_t i = 0; i < N; ++i) {
                if (candidates[i].size() > 1) candidates[i] = {candidates[i][1]};  // mid only
            }
            totalProbes = 1;
        }

        bool found = false;
        SamplePoint chosen;
        std::vector<size_t> idx(N, 0);
        for (size_t probe = 0; probe < totalProbes; ++probe) {
            SamplePoint ratSample;
            for (size_t i = 0; i < N; ++i) {
                ratSample.push(res.unknownSample.varOrder[i],
                               RealAlg::fromRational(candidates[i][idx[i]]));
            }
            bool allHold = true;
            for (const auto& c : consCopy) {
                auto norm = c.poly.toPrimitiveInteger(*kernel_);
                if (!norm.ok()) { allHold = false; break; }
                const Sign s = cacBackend_->signAt(norm.poly, ratSample);
                if (s == Sign::Unknown || !relationHolds(s, c.rel)) {
                    allHold = false;
                    break;
                }
            }
            if (allHold) {
                chosen = std::move(ratSample);
                found = true;
                break;
            }
            // increment idx (rightmost-first odometer)
            for (size_t pos = 0; pos < N; ++pos) {
                if (++idx[pos] < candidates[pos].size()) break;
                idx[pos] = 0;
            }
        }
        if (found) {
            std::unordered_map<VarId, mpq_class> rationalModel;
            for (size_t i = 0; i < chosen.varOrder.size(); ++i) {
                rationalModel.emplace(chosen.varOrder[i],
                                      chosen.values[i].rational);
            }
            satFastModel_ = std::move(rationalModel);
            return TheoryCheckResult::consistent();
        }
    }
#endif
    return std::nullopt;  // Unknown / no libpoly ⇒ fall through to Collins
}

// Stage 2: the CDCAC (Collins) engine. Always yields a definite verdict.
std::optional<TheoryCheckResult> NraSolver::stageCdcac(TheoryLemmaStorage& /*lemmaDb*/,
                                                       TheoryEffort /*effort*/) {
    if (xolver::env::diag("XOLVER_NRA_TOWER_DIAG"))
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
            if (xolver::env::diag("XOLVER_NRA_CDCAC_GUARD_DIAG"))
                std::fprintf(stderr, "[CDCAC-GUARD] declined: vars=%zu maxDeg=%d\n",
                             vars.size(), maxDeg);
            return TheoryCheckResult::unknown("cdcac-input-exceeds-libpoly-guard");
        }
    }
    // XOLVER_NRA_CAC_NO_COLLINS (differential): disable the Collins fallback so
    // CAC is the sole engine. Return Unknown (not nullopt) so the solver reports
    // unknown when CAC cannot decide, rather than a default/false verdict.
    static const bool noCollins = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_NO_COLLINS");
        if (e && *e && *e != '0') return true;
        const char* o = std::getenv("XOLVER_NRA_CAC_ONLY");   // legacy alias = all-efforts + no-collins
        return o && *o && *o != '0';
    }();
    if (noCollins) return TheoryCheckResult::unknown("cac-only-collins-disabled");
    return engine_.check();
}

// XOLVER_NRA_LINEARIZE incremental-linearization SAT LOOP (default OFF).
//
// Closes the linearization SAT loop for NRA (mirrors NiaSolver but for reals):
//
//   1. Read the LRA sibling's candidate relaxation model (numericAssignments).
//   2. VALIDATE it exactly: for every active original constraint (linear AND
//      nonlinear) compute the exact kernel sign at that rational point and
//      check the relation holds. If the model is non-empty and ALL hold, the
//      candidate is a genuine NRA model → return consistent() (invariant 1:
//      the verdict is backed by an exact-kernel check, never by the
//      abstraction alone).
//   3. Else REFINE: mirror active linear bounds + emit McCormick/square cuts
//      tangent at the CURRENT model point (model-construction), into lemmaDb.
//   4. LOOP CONTROL: if new cuts were emitted, return ONE as mkLemma (the rest
//      sit in lemmaDb). A Lemma result stops the pipeline BEFORE stageCdcac and
//      the SAT core adds the clause + re-solves, re-invoking the theory next
//      round (contract verified: ArithSolverBase::runReasonerPipeline returns
//      the first non-nullopt; CadicalTheoryPropagator enqueues the lemma clause
//      and re-solves). If the round cap is hit or no new cuts were generated
//      (dedup exhausted) and the model didn't validate, fall through to CDCAC.
//
// All diagnostics go to /tmp/linprobe.txt (CLI stderr is suppressed on the
// worker thread). CDCAC remains the backstop for everything this loop can't
// close. Flag OFF → returns nullopt immediately, identical to before.
std::optional<TheoryCheckResult> NraSolver::stageLinearizeProbe(TheoryLemmaStorage& lemmaDb,
                                                                TheoryEffort /*effort*/) {
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NRA_LINEARIZE");
        return e && (e[0]=='1'||e[0]=='t'||e[0]=='T'||e[0]=='y'||e[0]=='Y');
    }();
    if (!enabled) return std::nullopt;
    if (!registry_ || !linAdapter_) return std::nullopt;

    static const int kRefineCap = [] {
        int v = env::paramInt("XOLVER_NRA_LINEARIZE_CAP", 60);
        return v > 0 ? v : 60;
    }();

    std::ofstream lp("/tmp/linprobe.txt", std::ios::app);

    // Total degree of a polynomial via its monomial decomposition. Returns -1 if
    // the kernel cannot decompose it (e.g. non-integer coefficients).
    auto totalDegree = [&](PolyId p) -> int {
        auto termsOpt = kernel_->terms(p);
        if (!termsOpt) return -1;
        int maxDeg = 0;
        for (const auto& t : *termsOpt) {
            int d = 0;
            for (const auto& pe : t.powers) d += pe.second;
            if (d > maxDeg) maxDeg = d;
        }
        return maxDeg;
    };

    // --- Step 1: read the LRA sibling's candidate relaxation model. ----------
    std::unordered_map<std::string, mpq_class> model;
    bool modelFilled = false;
    if (linearSibling_) {
        auto m = linearSibling_->getModel();
        if (m) {
            for (const auto& [name, rv] : m->numericAssignments) {
                auto q = rv.tryAsRational();
                if (q) model.emplace(name, *q);  // skip algebraic/non-rational
            }
            modelFilled = !model.empty();
        }
    }
    // Diagnostic fingerprint of the BASE (non-aux) var values, to tell whether
    // the candidate model changes across rounds or the loop is stuck.
    mpq_class fp(0);
    int nBase = 0, nNonzeroBase = 0;
    for (const auto& [name, val] : model) {
        if (name.rfind("__nl_aux_", 0) == 0) continue;
        ++nBase;
        if (val != 0) ++nNonzeroBase;
        fp += val * val + val;  // order-independent-ish mix
    }
    if (std::getenv("XOLVER_NRA_LINEARIZE_DUMP") && modelFilled) {
        std::ofstream md("/tmp/linmodel.txt", std::ios::app);
        md << "--- model (nBase=" << nBase << " nNonzeroBase=" << nNonzeroBase
           << " total=" << model.size() << ") ---\n";
        int shown = 0;
        for (const auto& [name, val] : model) {
            if (shown++ >= 40) { md << "...\n"; break; }
            md << "  " << name << " = " << val.get_str() << "\n";
        }
        md.flush();
    }

    // --- Step 2: exact validation of EVERY active original constraint. -------
    // The kernel sgn() requires a COMPLETE assignment (every variable of the
    // polynomial must be present, else libpoly evaluates a non-constant value
    // and the rational-interval path corrupts the heap). Vars absent from the
    // candidate model are treated as 0 for the sign check (validation fallback)
    // by explicitly 0-filling each polynomial's variables. The check is over
    // the rational kernel sign, so a pass is a sound NRA model.
    int validated = 0, total = 0;
    bool allHold = true;
    {
        for (const auto& c : presolveConstraints_) {
            if (c.poly == NullPoly) continue;  // non-polynomial placeholder
            ++total;
            std::unordered_map<std::string, mpq_class> evalModel = model;
            for (const auto& vn : kernel_->variables(c.poly)) {
                evalModel.emplace(vn, mpq_class(0));  // 0-fill absent vars
            }
            int s = kernel_->sgn(c.poly, evalModel);
            bool ok = false;
            switch (c.rel) {
                case Relation::Eq:  ok = (s == 0); break;
                case Relation::Geq: ok = (s >= 0); break;
                case Relation::Leq: ok = (s <= 0); break;
                case Relation::Gt:  ok = (s > 0);  break;
                case Relation::Lt:  ok = (s < 0);  break;
                case Relation::Neq: ok = (s != 0); break;
            }
            if (ok) ++validated;
            else allHold = false;
        }
    }

    if (modelFilled && total > 0 && allHold) {
        lp << "[LINPROBE] round=" << linRefineRound_ << " model=filled"
           << " validated=" << validated << "/" << total
           << " newcuts=0 action=SAT\n";
        lp.flush();
        // Sound: the exact kernel sign validates ALL original constraints at a
        // concrete rational point. consistent() = SAT, stop the pipeline.
        return TheoryCheckResult::consistent();
    }

    // --- Step 3: refine. Mirror linear bounds + emit model-tangent cuts. -----
    std::vector<TheoryLemma> newLemmas;

    {
        std::vector<GenericActiveAssignment> gaas;
        gaas.reserve(activeRecords_.size());
        for (const auto& r : activeRecords_) {
            gaas.push_back({r.lit, r.atom, r.value});
        }
        auto mirrorLemmas = linAdapter_->mirrorActiveLinearBounds(gaas, TheoryId::LRA);
        for (auto& ml : mirrorLemmas) {
            if (!lemmaDb.contains(ml)) {
                lemmaDb.insertIfNew(ml);
                newLemmas.push_back(std::move(ml));
            }
        }
    }

    std::vector<ActiveNiaConstraint> activeNonlinear;
    for (const auto& pc : presolveConstraints_) {
        if (pc.poly == NullPoly) continue;
        if (totalDegree(pc.poly) < 2) continue;   // linear: already mirrored above
        activeNonlinear.push_back({pc.poly, pc.rel, pc.reason});
    }

    // Phase 4 (XOLVER_NRA_NLEXT_TANGENT_PERTURB): detect stuck-model. The
    // refinement loop is "stuck" when (a) the candidate-model fingerprint is
    // unchanged from the previous round AND (b) the previous round produced
    // zero NEW cuts (every cut was already in the cache). In that situation
    // every additional refinement at the same tangent point will keep hitting
    // the cache, and we converge to no progress. Perturbing the tangent point
    // breaks the loop by introducing fresh cuts at NEW points; convex tangent
    // is sound at any point, so this is safe.
    static const bool perturbEnabled = [] {
        const char* e = std::getenv("XOLVER_NRA_NLEXT_TANGENT_PERTURB");
        return e && (e[0]=='1'||e[0]=='t'||e[0]=='T'||e[0]=='y'||e[0]=='Y');
    }();
    // Cap perturbations per solve. Each perturbation injects fresh
    // tangent cuts that may extend the refinement loop without
    // converging; cap at a small number so we eventually fall through
    // to CDCAC rather than spinning. nra_150 regression analysis:
    // unbounded perturbation extended LIN refinement past its natural
    // termination on a SAT case, never reaching validator.
    static const int kPerturbCap = [] {
        int v = env::paramInt("XOLVER_NRA_NLEXT_TANGENT_PERTURB_CAP", 4);
        return v >= 0 ? v : 4;
    }();
    // Only activate perturbation AFTER the natural refinement loop has
    // had time to converge on its own. Earlier-round stuck states usually
    // resolve once McCormick/SquareCut emits its second-round refinement;
    // perturbation early disturbs SAT cases that would have validated in
    // a few more rounds (nra_150_sat regression analysis).
    static const int kPerturbMinRound = [] {
        // default 30 = half of default kRefineCap=60
        int v = env::paramInt("XOLVER_NRA_NLEXT_TANGENT_PERTURB_MINROUND", 30);
        return v >= 0 ? v : 30;
    }();
    bool isStuck = perturbEnabled && modelFilled &&
                   linRefineRound_ >= kPerturbMinRound &&
                   fp == lastLinFp_ && linLastNewCuts_ == 0 &&
                   static_cast<int>(linPerturbSeed_) < kPerturbCap;
    if (isStuck) {
        ++linStuckRounds_;
    } else {
        linStuckRounds_ = 0;
    }
    lastLinFp_ = fp;

    // Build the model passed to the linearizer. When stuck, perturb ONE
    // variable per round (round-robin via linPerturbSeed_) to a "diverse
    // seed" value. The pool of seed offsets is small and bounded:
    //   +1, -1, 0, +2, -2, model + small step, model - small step
    std::unordered_map<std::string, mpq_class> linModel = model;
    if (isStuck && !linModel.empty()) {
        std::vector<std::string> baseVars;
        baseVars.reserve(linModel.size());
        for (const auto& [name, _] : linModel)
            if (name.rfind("__nl_aux_", 0) != 0) baseVars.push_back(name);
        if (!baseVars.empty()) {
            std::sort(baseVars.begin(), baseVars.end()); // deterministic order
            uint32_t vIdx = linPerturbSeed_ % baseVars.size();
            uint32_t offIdx = (linPerturbSeed_ / baseVars.size()) % 7;
            const std::string& vn = baseVars[vIdx];
            const mpq_class& cur = linModel.at(vn);
            mpq_class perturbed;
            switch (offIdx) {
                case 0: perturbed = cur + 1; break;
                case 1: perturbed = cur - 1; break;
                case 2: perturbed = mpq_class(0); break;
                case 3: perturbed = cur + 2; break;
                case 4: perturbed = cur - 2; break;
                case 5: perturbed = cur + mpq_class(1, 2); break;   // +1/2
                case 6: perturbed = cur - mpq_class(1, 2); break;
                default: perturbed = cur;
            }
            linModel[vn] = perturbed;
            ++linPerturbSeed_;
        }
    }

    int nNonlinearNormalized = 0;
    if (!activeNonlinear.empty()) {
        NiaNormalizer normalizer(*kernel_);
        auto normalizedOpt = normalizer.normalize(activeNonlinear);
        if (normalizedOpt) {
            nNonlinearNormalized = static_cast<int>(normalizedOpt->size());
            // Tangent the cuts at the CURRENT (possibly perturbed) model point.
            // When the sibling has no model yet, fall back to the sign-bounded
            // linearizer (positivity assertions derive one-sided bounds → Family
            // 0 sign-only cuts fire) instead of the empty-bound path which
            // emitted ZERO sign cuts for sign-pinned mgc-class formulas.
            std::unordered_map<std::string, int> signMap;
            for (const auto& c : presolveConstraints_) {
                if (c.poly == NullPoly) continue;
                if (c.rel != Relation::Lt && c.rel != Relation::Leq &&
                    c.rel != Relation::Gt && c.rel != Relation::Geq) continue;
                auto termsOpt = kernel_->terms(c.poly);
                if (!termsOpt || termsOpt->size() != 1) continue;
                const auto& t = (*termsOpt)[0];
                if (t.powers.size() != 1 || t.powers[0].second != 1) continue;
                std::string vn = std::string(kernel_->varName(t.powers[0].first));
                int sign = 0;
                if (c.rel == Relation::Lt && t.coefficient < 0) sign = 1;
                else if (c.rel == Relation::Leq && t.coefficient < 0) sign = 1;
                else if (c.rel == Relation::Gt && t.coefficient > 0) sign = 1;
                else if (c.rel == Relation::Geq && t.coefficient > 0) sign = 1;
                else if (c.rel == Relation::Lt && t.coefficient > 0) sign = -1;
                else if (c.rel == Relation::Leq && t.coefficient > 0) sign = -1;
                else if (c.rel == Relation::Gt && t.coefficient < 0) sign = -1;
                else if (c.rel == Relation::Geq && t.coefficient < 0) sign = -1;
                if (sign != 0) signMap[vn] = sign;
            }
            auto lr = modelFilled
                ? linAdapter_->runLinearizerAtModel(*normalizedOpt, linModel, lemmaDb)
                : (signMap.empty()
                    ? linAdapter_->runLinearizer(*normalizedOpt, lemmaDb)
                    : linAdapter_->runLinearizerWithSignBounds(*normalizedOpt, signMap, lemmaDb));
            if (lr.status == LinearizationStatus::Lemma) {
                for (auto& item : lr.lemmas) {
                    if (!lemmaDb.contains(item.lemma)) {
                        lemmaDb.insertIfNew(item.lemma);
                        newLemmas.push_back(item.lemma);
                        if (item.cacheKey) linAdapter_->markEmitted(*item.cacheKey);
                    }
                }
            }
        }
    }

    int nNewCuts = static_cast<int>(newLemmas.size());
    linLastNewCuts_ = nNewCuts;  // Phase 4: feed into next-round stuck detection.

    // --- Step 4: loop control. -----------------------------------------------
    if (nNewCuts > 0 && linRefineRound_ < kRefineCap) {
        ++linRefineRound_;
        lp << "[LINPROBE] round=" << linRefineRound_
           << " model=" << (modelFilled ? "filled" : "empty")
           << " validated=" << validated << "/" << total
           << " nonlinearNormalized=" << nNonlinearNormalized
           << " newcuts=" << nNewCuts << " fp=" << fp.get_str() << " action=REFINE\n";
        lp.flush();
        // Return ONE lemma; the rest sit in lemmaDb. A Lemma stops the pipeline
        // before stageCdcac and forces a SAT-core re-solve (deferring CDCAC).
        return TheoryCheckResult::mkLemma(newLemmas.front());
    }

    lp << "[LINPROBE] round=" << linRefineRound_
       << " model=" << (modelFilled ? "filled" : "empty")
       << " validated=" << validated << "/" << total
       << " nonlinearNormalized=" << nNonlinearNormalized
       << " newcuts=" << nNewCuts
       << " fp=" << fp.get_str() << " action=CDCAC (cap=" << kRefineCap << ")\n";
    lp.flush();

    // Refinement exhausted (cap hit or dedup-saturated) and no validated model:
    // fall through to the CDCAC backstop (invariant 1: no unvalidated SAT).
    return std::nullopt;
}

} // namespace xolver
