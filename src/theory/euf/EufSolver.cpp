#include <cstdlib>
#include "util/EnvParam.h"
#include <chrono>
#include "theory/euf/EufSolver.h"
#include "util/SolveClock.h"
#include <stdexcept>
#include "theory/array/AniaProfile.h"
#include "theory/combination/CareGraph.h"
#include "theory/core/DebugTrace.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/datatype/DtModelValidator.h"
#include "expr/ir.h"
#include <cassert>
#include <algorithm>
#include <functional>
#include <climits>
#include <map>
#include <optional>
#include <tuple>

namespace xolver {

EufSolver::EufSolver() : egraph_(termManager_) {
    // 2026-06-02 PROMOTE XOLVER_EUF_PROP default-ON: EUF entailment propagation
    // makes EUF tell SAT about merge-implied equality atom truths, which closes
    // a subset of the Wisa-class false-SAT chain (xs-06-15 still needs DISEQ_WATCH
    // for full closure, but DISEQ_WATCH has an outstanding soundness bug — see
    // below — so it stays default-off). EUF_PROP alone is sound by construction
    // (propagation of an implied equality whose reasons are all asserted in the
    // current trail). Verified: unit 1098/1098, regression 670/670, 0 unsound.
    // Escape: XOLVER_EUF_PROP=0.
    //
    // 2026-06-02 PROMOTE XOLVER_UF_DISEQ_WATCH default-ON after the UFE專項
    // root-cause fix landed (BuiltinEval PendingMerge level tagging — earlier
    // commit). The wrong-UNSAT bug class (xs-10-08 + 4 Wisa siblings) was
    // caused by tryEvaluateBuiltin pushing PendingMerge with default level=0,
    // which left BuiltinEval-folded merges surviving every backtrack and
    // producing stale Congruence edges in the proof forest. Post-fix:
    //   ProofForest invariant checker reports 0 stale edges on xs-10-08.
    //   Wisa(30) DISEQ_WATCH=1: correct=6 unsound=0 (vs pre-fix unsound=4).
    //   unit 1098/1098, reg 670/670 default AND with DISEQ_WATCH=1.
    // Escape: XOLVER_UF_DISEQ_WATCH=0.
    auto envOnDefault = [](const char* name, bool def) {
        const char* e = std::getenv(name);
        if (!e) return def;
        return !(e[0] == '0' && e[1] == '\0');
    };
    diseqWatchEnabled_ = envOnDefault("XOLVER_UF_DISEQ_WATCH", true);
    eufPropEnabled_ = envOnDefault("XOLVER_EUF_PROP", true);
    // Default-ON (2026-06-02 DEEP-3): Track-3 UF function-interp collection.
    // Required by the QF_UFLIA combination soundness floor (COMB_VALIDATE_SAT)
    // and harmless when not consumed downstream (just populates getModel()
    // funcInterps). A/B escape: XOLVER_EUF_UF_MODEL=0 disables.
    ufModelEnabled_ = true;
    if (const char* e = std::getenv("XOLVER_EUF_UF_MODEL")) {
        ufModelEnabled_ = !(e[0] == '0' && e[1] == '\0');
    }
    // XOLVER_EUF_MINLEVEL_HEAP (default-OFF, array-deep B2): drain saturation mergeQueue_
    // with level-bucketed map; O(n^2) → O(n log L). Same order; targets QF_ANIA/QF_AX-swap blowup.
    minLevelHeapEnabled_ = xolver::env::diag("XOLVER_EUF_MINLEVEL_HEAP");
    // XOLVER_EUF_INCREMENTAL_PROP (Phase A, euf-deep): incremental entailment-prop scan.
    eufIncrementalProp_ = xolver::env::diag("XOLVER_EUF_INCREMENTAL_PROP");
    eufIncrementalVerify_ = xolver::env::diag("XOLVER_EUF_INCREMENTAL_PROP_VERIFY");
    if (eufIncrementalVerify_) eufIncrementalProp_ = true;  // verify implies on
    // XOLVER_EUF_PROP_DEDUP (Phase A v2): skip atoms with lemma already emitted at level<=current.
    eufPropDedup_ = xolver::env::diag("XOLVER_EUF_PROP_DEDUP");
    // XOLVER_AX_STORE_MODEL (default-OFF, array-deep A1): store-aware array model
    // construction. The baseline buildArrayModel collects each array's interp
    // from DIRECT select terms only, so an array defined by a store chain
    // (a2=store(a1,i,v), a3=store(a2,j,w), …) does NOT inherit the base's
    // entries — its interp is missing the inherited writes, so the model fails
    // the store-definition assertion and an otherwise-genuine sat floors to
    // unknown (the storecomm class). This pass derives each class interp by
    // following its store/const structure (inherit base entries + apply the
    // override), then overlays explicit reads. Verdict-SOUND: model
    // construction only; the arrayModelDefinitelyViolates floor still validates,
    // so a better model recovers genuine sats and a wrong one still floors.
    // #82 PROMOTED default-ON (escape XOLVER_AX_STORE_MODEL=0): closes the QF_AX
    // storecomm class (store-commutativity over named-intermediate towers) where
    // the baseline per-array select construction produced store-inconsistent
    // interps that floored genuine sats. Built once per candidate model (O(stores)
    // memoized, DAG-safe via cycle guard) -> low cost; verdict-sound (validator-
    // gated). Validated: reg 806/806 0-unsound 0-regression, QF_AX sample +8
    // solved 0-unsound 0-lost (with XOLVER_AX_ROW2_DISEQ).
    storeModelEnabled_ = xolver::env::flag("XOLVER_AX_STORE_MODEL", true);
    // #85 model-driven array refinement (default-OFF). See header.
    arrayRefineEnabled_ = xolver::env::diag("XOLVER_AX_REFINE");
    // E2/E3 profile triage (default-OFF): lightweight counters + chrono.
    hotProfileEnabled_ = xolver::env::diag("XOLVER_EUF_HOTPROFILE");
    // L3 (default-OFF): array-axiom saturation fixpoint (nested read-over-write).
    arrayFixpointEnabled_ = xolver::env::diag("XOLVER_AX_FIXPOINT");
    initializeBoolConstants();
}

EufSolver::~EufSolver() {
    if (hotProfileEnabled_ && hotProfile_.checkCalls > 0) {
        // E2/E3 hot-path triage dump (XOLVER_EUF_HOTPROFILE). Goal: identify
        // whether EUF (>50% time inside check) is the QG-classification /
        // eq_diamond perf-wall bottleneck, or whether SAT/CDCL outside check()
        // dominates (which would route the lane closure to SAT backend).
        std::cerr << "[EUF-HOTPROFILE]"
                  << " checks=" << hotProfile_.checkCalls
                  << " checkUs=" << hotProfile_.checkUs
                  << " saturationUs=" << hotProfile_.saturationUs
                  << " explainUs=" << hotProfile_.explainUs
                  << " entailUs=" << hotProfile_.entailmentUs
                  << " registerSigUs=" << hotProfile_.registerSigUs
                  << " merges=" << hotProfile_.mergesProcessed
                  << " explains=" << hotProfile_.explainCalls
                  << " entailScanRecs=" << hotProfile_.entailmentScanRecs
                  << " entailEmitted=" << hotProfile_.entailmentEmitted
                  << "\n";
    }
}


std::vector<std::pair<SharedTermId, SharedTermId>>
EufSolver::collectArrangeableUfArgPairs(
    const std::function<bool(SharedTermId, SharedTermId)>& valueEqual,
    const std::function<bool(SharedTermId, SharedTermId)>& appsResultApart) const {
    std::vector<std::pair<SharedTermId, SharedTermId>> pairs;
    // Reverse map: EufTermId -> SharedTermId (interface constants/bridge vars).
    std::unordered_map<EufTermId, SharedTermId> eufToShared;
    eufToShared.reserve(sharedTermToEufTerm_.size());
    for (const auto& [s, t] : sharedTermToEufTerm_) eufToShared.emplace(t, s);

    // Application terms grouped by (symbol, arity), skipping arithmetic builtins
    // (#builtin.*) — interpreted by the arith solver, not EUF congruence. User
    // UF + #array.select/store are congruence-relevant.
    std::unordered_map<uint64_t, std::vector<EufTermId>> byKind;
    for (EufTermId t = 0; t < static_cast<EufTermId>(termManager_.termCount()); ++t) {
        const auto& n = termManager_.node(t);
        if (n.args.empty()) continue;
        if (termManager_.symbolName(n.symbol).rfind("#builtin.", 0) == 0) continue;
        uint64_t key = (static_cast<uint64_t>(n.symbol) << 8) | (n.args.size() & 0xff);
        byKind[key].push_back(t);
    }
    auto sharedOf = [&](EufTermId t) -> SharedTermId {
        auto it = eufToShared.find(t);
        return it == eufToShared.end() ? static_cast<SharedTermId>(-1) : it->second;
    };
    // #77: an APPLICATION's result shared term is not the app EufTerm itself but
    // a separate bridge/constant node MERGED into the app's eclass (ufbridge =
    // f(args)). Map each eclass rep to one shared term in it so appsResultApart
    // can compare the two apps' bridged result values.
    std::unordered_map<EClassId, SharedTermId> repToShared;
    for (const auto& [s, t] : sharedTermToEufTerm_) {
        if (t == NullEufTerm) continue;
        repToShared.emplace(egraph_.rep(t), s);
    }
    auto resultSharedOf = [&](EufTermId app) -> SharedTermId {
        auto it = repToShared.find(egraph_.rep(app));
        return it == repToShared.end() ? static_cast<SharedTermId>(-1) : it->second;
    };
    // Two applications are a genuine arrangement obligation only if they are
    // forced apart. The strict source is an EUF-level (distinct ...) putting
    // their classes apart (appsKnownDisequal): then arranging their args equal
    // forces a congruence contradicting the disequality. The #77 source, when
    // the caller supplies appsResultApart (split path only), additionally admits
    // apps whose bridged RESULTS are ARITH-apart (e.g. f(a) < f(b), which EUF
    // does not see) — sound because the emitted split lets the search resolve
    // breakability (refute both branches when the args are arith-forced equal).
    // The certificate floor omits appsResultApart and stays strict (a
    // coincidental arith-apart with breakable args must not over-floor a sat).
    auto appsKnownDisequal = [&](EufTermId t1, EufTermId t2) -> bool {
        auto match = [&](const ActiveDisequality& d) {
            return (egraph_.same(t1, d.lhs) && egraph_.same(t2, d.rhs)) ||
                   (egraph_.same(t1, d.rhs) && egraph_.same(t2, d.lhs));
        };
        for (const auto& d : disequalities_)       if (match(d)) return true;
        for (const auto& d : sharedDisequalities_) if (match(d)) return true;
        return false;
    };
    for (auto& [key, apps] : byKind) {
        (void)key;
        for (size_t p = 0; p < apps.size(); ++p) {
            for (size_t q = p + 1; q < apps.size(); ++q) {
                EufTermId t1 = apps[p], t2 = apps[q];
                if (egraph_.same(t1, t2)) continue;
                // Forced apart by an EUF distinct, or (#77, split path only) by
                // ARITH on the apps' bridged result shared terms.
                bool apart = appsKnownDisequal(t1, t2);
                if (!apart && appsResultApart) {
                    SharedTermId r1 = resultSharedOf(t1), r2 = resultSharedOf(t2);
                    if (r1 != static_cast<SharedTermId>(-1) &&
                        r2 != static_cast<SharedTermId>(-1) &&
                        r1 != r2 && appsResultApart(r1, r2))
                        apart = true;
                }
                if (!apart) continue;
                const auto& a1 = termManager_.node(t1).args;
                const auto& a2 = termManager_.node(t2).args;
                if (a1.size() != a2.size()) continue;
                // Every differing position must be a SHARED, value-equal pair for
                // arranging to force congruence; otherwise the pair is not
                // arrangeable and we skip it (do not split).
                std::vector<std::pair<SharedTermId, SharedTermId>> diff;
                bool arrangeable = true;
                for (size_t i = 0; i < a1.size(); ++i) {
                    if (egraph_.same(a1[i], a2[i])) continue;
                    SharedTermId s1 = sharedOf(a1[i]), s2 = sharedOf(a2[i]);
                    if (s1 == static_cast<SharedTermId>(-1) ||
                        s2 == static_cast<SharedTermId>(-1) ||
                        !valueEqual(s1, s2)) { arrangeable = false; break; }
                    diff.emplace_back(s1, s2);
                }
                if (arrangeable && !diff.empty())
                    for (auto& d : diff) pairs.push_back(d);
            }
        }
    }
    return pairs;
}


void EufSolver::push() {
    scopeLimits_.push_back(trail_.size());
    scopeSnapshots_.push_back(egraph_.snapshot());
}

void EufSolver::pop(uint32_t n) {
    while (n-- && !scopeLimits_.empty()) {
        size_t limit = scopeLimits_.back();
        EGraphSnapshot snap = scopeSnapshots_.back();

        trail_.resize(limit);

        // remove disequalities whose assignment was popped
        auto dit = std::remove_if(disequalities_.begin(), disequalities_.end(),
            [limit](const auto& d) { return d.trailIndex >= limit; });
        disequalities_.erase(dit, disequalities_.end());

        mergeQueue_.clear();

        egraph_.rollback(snap);

        // Reset bool marks: recompute from current egraph roots
        for (auto& info : classInfo_) {
            info.boolMark = BoolConstMark::None;
        }
        if (trueTerm_ != NullEufTerm) {
            classInfo(egraph_.rep(trueTerm_)).boolMark = BoolConstMark::True;
        }
        if (falseTerm_ != NullEufTerm) {
            classInfo(egraph_.rep(falseTerm_)).boolMark = BoolConstMark::False;
        }

        pendingConflict_.reset();
        pendingUnknown_ = false;

        // Decision-level egraph boundaries are scoped to a single solve; a scope
        // pop returns to the assertion stack (decision level 0), so discard them.
        egraphBoundaries_.clear();

        scopeLimits_.pop_back();
        scopeSnapshots_.pop_back();
    }
}

void EufSolver::reset() {
    modelSnapshot_.reset();
    trail_.clear();
    scopeLimits_.clear();
    scopeSnapshots_.clear();
    egraphBoundaries_.clear();
    disequalities_.clear();
    pendingConflict_.reset();
    pendingUnknown_ = false;
    termManager_.clear();
    egraph_.clear();
    sharedTermToEufTerm_.clear();
    sharedDisequalities_.clear();

    classInfo_.clear();
    mergeQueue_.clear();
    trueTerm_ = NullEufTerm;
    falseTerm_ = NullEufTerm;

    arrayReasoner_.reset();
    dtReasoner_.reset();

    initializeBoolConstants();
}


void EufSolver::recordEgraphBoundary(int level) {
    // Record the egraph snapshot as the boundary for `level` (state before this
    // level's merges) the first time check() begins processing merges at this
    // level. Boundaries are kept sorted ascending; since check() processes
    // merges in ascending level order, levels arrive non-decreasing.
    if (!egraphBoundaries_.empty() && egraphBoundaries_.back().level >= level) return;
    egraphBoundaries_.push_back({level, egraph_.snapshot()});
}

void EufSolver::backtrackToLevel(int target) {
    currentLevel_ = target;
    // Force a full entailment sweep on the next propagation call: the assigned
    // set changed and the mergeRecord count is about to regress, so the
    // class-touch dirty index built from prior merges is no longer authoritative.
    forceFullEntailmentScan_ = true;
    lastSeenMergeRecord_ = 0;
    // XOLVER_EUF_PROP_DEDUP: invalidate emissions at levels > target. The lemmas
    // are still in SAT's lemmaDb (which has its own backtrack semantics), but
    // their entailment condition may now be unmet so we must consider re-emitting.
    if (eufPropDedup_) {
        for (auto& lvl : emittedAtomLevel_) {
            if (lvl > target) lvl = -1;
        }
    }

    // Trail: keep entries with level <= target. The SAT decision trail is
    // level-ordered (ascending), so the kept entries are a prefix.
    size_t keep = trail_.size();
    for (size_t i = 0; i < trail_.size(); ++i) {
        if (trail_[i].level > target) { keep = i; break; }
    }
    trail_.resize(keep);

    // Drop disequalities / shared disequalities / queued merges above target.
    auto dit = std::remove_if(disequalities_.begin(), disequalities_.end(),
        [target](const auto& d) { return d.level > target; });
    disequalities_.erase(dit, disequalities_.end());

    auto sdIt = std::remove_if(sharedDisequalities_.begin(), sharedDisequalities_.end(),
        [target](const auto& d) { return d.level > target; });
    sharedDisequalities_.erase(sdIt, sharedDisequalities_.end());

    auto mqIt = std::remove_if(mergeQueue_.begin(), mergeQueue_.end(),
        [target](const auto& m) { return m.level > target; });
    mergeQueue_.erase(mqIt, mergeQueue_.end());

    // Egraph: restore the boundary of the SMALLEST level > target — its
    // egraphBefore is the state after all level-<=target merges (boundaries are
    // recorded in level order, and the saturation applies merges level-ordered,
    // so the size-based undo is level-monotonic). If no level > target produced
    // merges, the egraph is already at the target state.
    const EgraphBoundary* restore = nullptr;
    for (const auto& b : egraphBoundaries_) {
        if (b.level > target) { restore = &b; break; }
    }
    if (restore) egraph_.rollback(restore->egraphBefore);
    while (!egraphBoundaries_.empty() && egraphBoundaries_.back().level > target)
        egraphBoundaries_.pop_back();

    // SECOND PASS — level-filter cleanup. The count-based snapshot rollback
    // above assumes mergeRecords_ are inserted in monotonically non-decreasing
    // level order. Combination interface (dis)equalities can violate that
    // assumption: an assertInterfaceEquality at SAT level L_late may be queued
    // and processed AFTER a higher-level merge was already inserted into
    // mergeRecords_. The level=L_late record then sits AFTER the level=high
    // record in mergeRecords_, so the count-based truncation either keeps the
    // high-level merge (leaving a stale congruence whose arg merge was rolled
    // back) or drops a low-level merge (leaving a stale congruence whose
    // dependency was kept but the congruence itself is gone). Either way, the
    // proof forest references edges whose semantic justification doesn't hold.
    //
    // Walk mergeRecords_ from the END, dropping any entry with level > target.
    // Mirror the drop in the proof forest via rollbackByLevel(target). The
    // egraph union-find was already rolled back to the boundary snapshot, so
    // any merge dropped here had its UF effect already undone; we just need to
    // synchronize the mergeRecords_ and proofForest_ trail with that state.
    // See project-euf-proof-forest-rollback memory for the full diagnosis.
    egraph_.dropMergeRecordsAboveLevel(target);
    egraph_.proofForestMutable().rollbackByLevel(target);

    // clean scope stack if needed
    while (!scopeLimits_.empty() && scopeLimits_.back() > trail_.size()) {
        scopeLimits_.pop_back();
        scopeSnapshots_.pop_back();
    }

    // Reset bool marks: recompute from current egraph roots
    for (auto& info : classInfo_) {
        info.boolMark = BoolConstMark::None;
    }
    if (trueTerm_ != NullEufTerm) {
        classInfo(egraph_.rep(trueTerm_)).boolMark = BoolConstMark::True;
    }
    if (falseTerm_ != NullEufTerm) {
        classInfo(egraph_.rep(falseTerm_)).boolMark = BoolConstMark::False;
    }

    pendingConflict_.reset();
    pendingUnknown_ = false;
    checkProofForestInvariants("backtrackToLevel-exit");
}

void EufSolver::initializeBoolConstants() {
    trueTerm_ = termManager_.internTrueConstant();
    falseTerm_ = termManager_.internFalseConstant();
    egraph_.setTrueTerm(trueTerm_);
    egraph_.setFalseTerm(falseTerm_);
    egraph_.ensureTermRegistered(trueTerm_, mergeQueue_);
    egraph_.ensureTermRegistered(falseTerm_, mergeQueue_);

    if (trueTerm_ != NullEufTerm) {
        classInfo(egraph_.rep(trueTerm_)).boolMark = BoolConstMark::True;
    }
    if (falseTerm_ != NullEufTerm) {
        classInfo(egraph_.rep(falseTerm_)).boolMark = BoolConstMark::False;
    }
}

EufSolver::EClassInfo& EufSolver::classInfo(EClassId id) {
    if (classInfo_.size() <= id) classInfo_.resize(id + 1);
    return classInfo_[id];
}

EufSolver::BoolConstMark EufSolver::mergeBoolMark(BoolConstMark a, BoolConstMark b) {
    if (a == BoolConstMark::Both || b == BoolConstMark::Both) return BoolConstMark::Both;
    if (a == BoolConstMark::None) return b;
    if (b == BoolConstMark::None) return a;
    if (a == b) return a;
    return BoolConstMark::Both;
}

std::vector<SatLit> EufSolver::allActiveReasons() const {
    std::vector<SatLit> reasons;
    reasons.reserve(trail_.size() + disequalities_.size() + sharedDisequalities_.size());
    for (const auto& e : trail_) {
        reasons.push_back(e.lit);
    }
    for (const auto& d : disequalities_) {
        reasons.push_back(d.reason);
    }
    for (const auto& d : sharedDisequalities_) {
        reasons.push_back(d.reason);
    }
    std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    reasons.erase(std::unique(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), reasons.end());
    return reasons;
}

void EufSolver::onEclassMerged(EClassId kept, EClassId killed) {
    auto& kInfo = classInfo(kept);
    auto& dInfo = classInfo(killed);

    BoolConstMark merged = mergeBoolMark(kInfo.boolMark, dInfo.boolMark);
    kInfo.boolMark = merged;
    dInfo.boolMark = BoolConstMark::None;

    // Both -> conflict
    if (merged == BoolConstMark::Both) {
        auto er = egraph_.explainEquality(trueTerm_, falseTerm_);
        if (xolver::env::diag("EUF_DIAG")) {
            std::cerr << "[EUF-DIAG] BOOL-BOTH kept=" << kept << " killed=" << killed
                      << " kMark=" << (int)kInfo.boolMark << " dMark=" << (int)dInfo.boolMark
                      << " explainTF.ok=" << er.ok << " chain=" << er.reasons.size()
                      << " trueRep=" << egraph_.rep(trueTerm_) << " falseRep=" << egraph_.rep(falseTerm_) << "\n";
        }
        if (er.ok && egraph_.same(trueTerm_, falseTerm_)) {
            pendingConflict_ = TheoryConflict{std::move(er.reasons)};
        } else {
            // SOUNDNESS: a Both boolMark means this class is tagged as
            // containing a term equal to `true` AND a term equal to `false`.
            // But the mark is propagated by class-merge bookkeeping
            // (mergeBoolMark) which, in rare orderings driven by array
            // Row1/Row2 reasoning over compound/bridge indices, can tag a
            // class Both even though the genuine `true` and `false` constant
            // terms are NOT in the same egraph class (here trueRep != falseRep,
            // so explainEquality(true,false) correctly reports !ok — there is
            // no real true == false derivation). Emitting allActiveReasons() as
            // a conflict in that case is UNSOUND: it asserts that the current,
            // perfectly satisfiable assignment is contradictory, producing a
            // spurious UNSAT (observed as an intermittent false-unsat on
            // QF_A(UF)L(I/R)A formulas with purified compound array indices).
            //
            // Only emit a conflict when true and false are genuinely merged
            // (the `ok` branch above, which carries a real reason chain). When
            // they are not, there is no sound conflict to report; fall through
            // without setting pendingConflict_. Congruence continues normally
            // and the model is validated by the exact kernel before any SAT is
            // returned, so soundness is preserved. At worst this is incomplete
            // (the genuine conflict, if any, is found via another path or the
            // result is Unknown) — never a wrong verdict.
            NO_DBG << "[EUF] BOOL-BOTH mark without a real true==false merge "
                      "(trueRep != falseRep); suppressing unsound fallback conflict\n";
        }

    }
}

// ---------------------------------------------------------------------------
// assertLit
// ---------------------------------------------------------------------------

void EufSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) {
    if (!std::holds_alternative<EufAtomPayload>(atom.payload)) return;
    const auto& payload = std::get<EufAtomPayload>(atom.payload);

    currentLevel_ = std::max(currentLevel_, level);

    // Everything this assertLit queues (term-registration congruences + the
    // asserted merge) belongs to `level`; tag from here so the level-ordered
    // saturation and the level-aware backtrack treat it consistently.
    size_t mqBefore = mergeQueue_.size();
    auto tagFromHere = [&]() {
        for (size_t i = mqBefore; i < mergeQueue_.size(); ++i) mergeQueue_[i].level = level;
    };

    // Lazily intern true/false constants
    EufTermId trueTerm = termManager_.internTrueConstant();
    EufTermId falseTerm = termManager_.internFalseConstant();
    egraph_.setTrueTerm(trueTerm);
    egraph_.setFalseTerm(falseTerm);
    egraph_.ensureTermRegistered(trueTerm, mergeQueue_);
    egraph_.ensureTermRegistered(falseTerm, mergeQueue_);

    // Update our cached true/false roots if they changed
    if (trueTerm_ == NullEufTerm) {
        trueTerm_ = trueTerm;
        classInfo(egraph_.rep(trueTerm_)).boolMark = BoolConstMark::True;
    }
    if (falseTerm_ == NullEufTerm) {
        falseTerm_ = falseTerm;
        classInfo(egraph_.rep(falseTerm_)).boolMark = BoolConstMark::False;
    }

    // Intern lhs/rhs (monotonic)
    EufTermId lhs = termManager_.intern(payload.lhs, *coreIr_);
    EufTermId rhs = termManager_.intern(payload.rhs, *coreIr_);
    if (lhs == NullEufTerm || rhs == NullEufTerm) {
        pendingUnknown_ = true;
        tagFromHere();
        return;
    }

    egraph_.ensureTermRegistered(lhs, mergeQueue_);
    egraph_.ensureTermRegistered(rhs, mergeQueue_);

    if (payload.kind == EufAtomKind::BoolTermAsFormula) {
        EufTermId target = value ? trueTerm : falseTerm;
        trail_.push_back({level, reason, atom, value});
        MergeReason mr;
        mr.kind = MergeReasonKind::AssertedEquality;
        mr.lit = reason;
        mergeQueue_.push_back({lhs, target, mr});
        tagFromHere();
        return;
    }

    bool isEq = false;
    if (payload.rel == Relation::Eq) {
        isEq = value;
    } else if (payload.rel == Relation::Neq) {
        isEq = !value;
    } else {
        tagFromHere();
        return;
    }

    size_t trailIdx = trail_.size();
    trail_.push_back({level, reason, atom, value});

    if (isEq) {
        MergeReason mr;
        mr.kind = MergeReasonKind::AssertedEquality;
        mr.lit = reason;
        mergeQueue_.push_back({lhs, rhs, mr});
    } else {
        disequalities_.push_back({lhs, rhs, reason, level, trailIdx});
    }
    tagFromHere();
}

// ---------------------------------------------------------------------------
// check — 唯一 saturation loop
// ---------------------------------------------------------------------------


// ---------------------------------------------------------------------------
// Nelson-Oppen combination hooks
// ---------------------------------------------------------------------------

EufTermId EufSolver::internSharedConstant(SharedTermId s) {
    auto it = sharedTermToEufTerm_.find(s);
    if (it != sharedTermToEufTerm_.end()) {
        return it->second;
    }

    if (!sharedTermRegistry_ || !coreIr_) return NullEufTerm;
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return NullEufTerm;

    EufTermId t = termManager_.intern(st->coreExpr, const_cast<CoreIr&>(*coreIr_));
    if (t != NullEufTerm) {
        sharedTermToEufTerm_[s] = t;
        egraph_.ensureTermRegistered(t, mergeQueue_);
    }
    return t;
}

EufTermId EufSolver::internEufExpr(ExprId eid) {
    if (!coreIr_) return NullEufTerm;
    EufTermId t = termManager_.intern(eid, const_cast<CoreIr&>(*coreIr_));
    if (t != NullEufTerm) {
        egraph_.ensureTermRegistered(t, mergeQueue_);
    }
    return t;
}

TheoryCheckResult EufSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    currentLevel_ = std::max(currentLevel_, level);
    size_t mqBefore = mergeQueue_.size();
    auto tagFromHere = [&]() {
        for (size_t i = mqBefore; i < mergeQueue_.size(); ++i) mergeQueue_[i].level = level;
    };

    EufTermId ta = internSharedConstant(a);
    EufTermId tb = internSharedConstant(b);
    if (ta == NullEufTerm || tb == NullEufTerm) {
        tagFromHere();
        return TheoryCheckResult::unknown();
    }

    MergeReason mr;
    mr.kind = MergeReasonKind::AssertedEquality;
    mr.lit = reason;
    mergeQueue_.push_back({ta, tb, mr});
    tagFromHere();
    return TheoryCheckResult::consistent();
}

TheoryCheckResult EufSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    currentLevel_ = std::max(currentLevel_, level);
    size_t mqBefore = mergeQueue_.size();

    EufTermId ta = internSharedConstant(a);
    EufTermId tb = internSharedConstant(b);
    for (size_t i = mqBefore; i < mergeQueue_.size(); ++i) mergeQueue_[i].level = level;
    if (ta == NullEufTerm || tb == NullEufTerm) {
        return TheoryCheckResult::unknown();
    }

    if (egraph_.same(ta, tb)) {
        auto er = egraph_.explainEquality(ta, tb);
        if (xolver::env::diag("EUF_DIAG")) {
            const auto* sa = sharedTermRegistry_ ? sharedTermRegistry_->get(a) : nullptr;
            const auto* sb = sharedTermRegistry_ ? sharedTermRegistry_->get(b) : nullptr;
            auto dump = [&](const char* tag, auto s) {
                std::cerr << " " << tag << "{";
                if (s && coreIr_) {
                    const auto& e = coreIr_->get(s->coreExpr);
                    std::cerr << "expr=" << (int)s->coreExpr << " kind=" << (int)e.kind;
                    if (auto* iv = std::get_if<int64_t>(&e.payload.value)) std::cerr << " int=" << *iv;
                    else if (auto* sv = std::get_if<std::string>(&e.payload.value)) std::cerr << " sym=" << *sv;
                    std::cerr << " nch=" << e.children.size();
                }
                std::cerr << "}";
            };
            std::cerr << "[EUF-DIAG] IFACE-DISEQ-IMMEDIATE sharedA=" << a << " sharedB=" << b
                      << " ta=" << ta << " tb=" << tb << " sameSharedId=" << (a == b);
            dump("A", sa); dump("B", sb);
            std::cerr << " ok=" << er.ok << " chain=" << er.reasons.size() << "\n";
        }
        if (er.ok) {
            er.reasons.push_back(reason);
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
        }
        auto reasons = allActiveReasons();
        reasons.push_back(reason);
        return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
    }

    sharedDisequalities_.push_back({ta, tb, reason, level, trail_.size()});
    return TheoryCheckResult::consistent();
}

bool EufSolver::areSharedTermsMerged(SharedTermId a, SharedTermId b) const {
    if (a == b) return true;
    // Only consult terms that have ALREADY been interned as shared constants.
    // Interning is a mutating operation (registers signatures / enqueues
    // merges), so a const observer must not trigger it. If a shared scalar has
    // never been interned, it cannot be merged with anything on the EUF side
    // yet -> report not-merged (conservative).
    auto ia = sharedTermToEufTerm_.find(a);
    auto ib = sharedTermToEufTerm_.find(b);
    if (ia == sharedTermToEufTerm_.end() || ib == sharedTermToEufTerm_.end())
        return false;
    if (ia->second == NullEufTerm || ib->second == NullEufTerm) return false;
    return egraph_.same(ia->second, ib->second);
}

std::vector<TheorySolver::SharedEqualityPropagation>
EufSolver::getDeducedSharedEqualities() {
    std::vector<SharedEqualityPropagation> result;
    if (!sharedTermRegistry_) return result;

    const auto& allShared = sharedTermRegistry_->allSharedTerms();
    const size_t N = allShared.size();

    // iter-95 perf fix: pre-intern all shared terms ONCE before the O(N²)
    // pair loop. The previous implementation re-interned allShared[j] for
    // every pair (i,j), turning interning into an O(N²) cost. For Dartagnan
    // (14K Boolean vars, ~100s shared terms after promotion) and similar
    // combined-logic cases, this saves up to N×(N−1)/2 interning calls per
    // getDeducedSharedEqualities invocation. Interning is hash+lookup, not
    // free — and getDeducedSharedEqualities is hit on every Nelson-Oppen
    // exchange round, so the cost compounds.
    //
    // Soundness invariant unchanged: interning is referentially transparent
    // (same SharedTermId → same EufTermId), so caching the result for the
    // duration of one call cannot change behavior. Egraph state observed in
    // .same() / .explainEquality() is identical to the unbatched path.
    std::vector<EufTermId> interned(N);
    for (size_t k = 0; k < N; ++k) {
        interned[k] = internSharedConstant(allShared[k]);
    }

    for (size_t i = 0; i < N; ++i) {
        EufTermId ti = interned[i];
        if (ti == NullEufTerm) continue;
        for (size_t j = i + 1; j < N; ++j) {
            EufTermId tj = interned[j];
            if (tj == NullEufTerm) continue;
            // Care-graph prune (XOLVER_COMB_CAREGRAPH): skip pairs no theory
            // cares about. Done AFTER interning (so egraph state is identical
            // to the unpruned path) but before the expensive same/explain. An
            // EUF-merged pair is always care-relevant (it was connected via an
            // Eq/Distinct or a congruence arg), so this prunes only inert,
            // never-equal pairs — no real propagation is lost.
            if (careGraph_ && !careGraph_->caresPair(allShared[i], allShared[j]))
                continue;
            if (egraph_.same(ti, tj)) {
                auto er = egraph_.explainEquality(ti, tj);
                if (er.ok) {
                    result.push_back({allShared[i], allShared[j], std::move(er.reasons)});
                }
            }
        }
    }

    return result;
}


} // namespace xolver
