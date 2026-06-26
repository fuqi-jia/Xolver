#include "util/MpqUtils.h"
#include "theory/arith/lia/LiaSolver.h"
#include "util/MpqUtils.h"
#include "util/EnvParam.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/arith/Reasoner.h"
#include "theory/arith/linear/SimplexDiseqSplitter.h"
#include "theory/arith/linear/LinearConstraintNormalizer.h"
#include "theory/arith/lia/GomoryCut.h"
#include "theory/arith/lia/LiaSolverDetail.h"  // isIntegerLinearForm / roundNearest (shared across split TUs)
#include "theory/arith/nia/reasoners/DioReasoner.h"
#include <cassert>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <filesystem>
#include <cstdlib>
#include <sstream>
#include <map>

namespace xolver {

// isIntegerLinearForm() moved to LiaSolverDetail.h so the split LiaSolver_*.cpp
// translation units can share it (integer coefficients + integer rhs ⇒ the aux
// var s = Σ coeff·x − rhs is integer too, enabling exact strict→±1 tightening).

LiaSolver::LiaSolver() {
    const char* env = std::getenv("XOLVER_LIA_DUMP_DIR");
    if (env) {
        dumpCounter_ = 0;
    }
    repairEnabled_ = xolver::env::flag("XOLVER_LIA_REPAIR");
    cutsEnabled_ = xolver::env::flag("XOLVER_LIA_CUTS");
    gmiCutsEnabled_ = xolver::env::flag("XOLVER_LIA_GMI_CUTS");
    // XOLVER_LIA_INCREMENTAL (default OFF): incremental simplex replay instead
    // of the full-rebuild-every-check baseline. The baseline resets all bounds
    // and re-asserts the entire theory trail on every stageCore() call — O(checks
    // x trail) — which dominates on large incremental instances (convert,
    // nec-smt residual, mathsat FISCHER): lia.core is invoked hundreds of times
    // and each call re-pivots from scratch. Incremental mode applies only new
    // trail entries (appliedCursor_) and relies on gs_ push/pop + backtrackToLevel
    // (already exercised incrementally by LRA) to undo bounds. activeAtoms_/
    // disequalities_ are maintained by assertLit in both modes, so only the
    // simplex bound application differs.
    incrementalEnabled_ = xolver::env::flag("XOLVER_LIA_INCREMENTAL");
    impliedEqEnabled_ = xolver::env::flag("XOLVER_SIMPLEX_IMPLIED_EQ");
    dioTightenEnabled_ = xolver::env::flag("XOLVER_LIA_DIO");
    // Phase 2: single core reasoner (incremental replay + interface eqs +
    // simplex + integrality + branch).
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "lia.core",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCore(db, e); }));
}

LiaSolver::~LiaSolver() {
#ifdef XOLVER_LIA_PROFILE
    if (profile_.checkCalls > 0) {
        profile_.dump();
    }
#endif
}

void LiaSolver::onPush() {
    gs_.push();
}

void LiaSolver::onPop(uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) {
        gs_.pop();
    }
}

void LiaSolver::onReset() {
    theoryTrail_.clear();
    trailIndexBySatVar_.clear();
    appliedCursor_ = 0;
    activeAtoms_.clear();
    disequalities_.clear();
    integerVars_.clear();   // incremental mode: grow-only set, cleared on full reset
    pendingConflict_.reset();
    diseqBranchAuthorized_.clear();
    repairModel_.reset();
    cutsThisSolve_ = 0;
    gs_.resetActiveBounds();
    entailmentProps_.clear();
    entailmentEmittedKeys_.clear();
}

void LiaSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) {
    if (!std::holds_alternative<LinearAtomPayload>(atom.payload)) return;

    const auto& payload = std::get<LinearAtomPayload>(atom.payload);
    // LIA bounds are rational (integer-theory inputs never produce algebraic
    // RHS); asRational() is the standard conversion at this boundary.
    const mpq_class& rhs = payload.rhs.asRational();
    int auxVar = manager_.getOrCreateAuxVar(gs_, payload.lhs, rhs);
    Relation effectiveRel = value ? payload.rel : negateRelation(payload.rel);
    bool isDiseq = (effectiveRel == Relation::Neq);

    auto idxIt = trailIndexBySatVar_.find(atom.satVar);
    if (idxIt != trailIndexBySatVar_.end()) {
        auto& e = theoryTrail_[idxIt->second];
        if (e.isDiseq) {
            auto it = std::remove_if(disequalities_.begin(), disequalities_.end(),
                [&e](const auto& d) { return d.lit == e.lit; });
            disequalities_.erase(it, disequalities_.end());
        } else {
            auto it = std::remove_if(activeAtoms_.begin(), activeAtoms_.end(),
                [&e](const auto& a) { return a.lit == e.lit; });
            activeAtoms_.erase(it, activeAtoms_.end());
        }
        e = {level, assertedLit, atom, value, auxVar, isDiseq};
        if (isDiseq) {
            disequalities_.push_back({auxVar, payload.lhs, rhs, assertedLit});
        } else {
            activeAtoms_.push_back({atom.exprId, auxVar, payload.rel, value, payload.lhs, rhs, assertedLit});
        }
        return;
    }
    trailIndexBySatVar_[atom.satVar] = theoryTrail_.size();
    theoryTrail_.push_back({level, assertedLit, atom, value, auxVar, isDiseq});
    if (isDiseq) {
        disequalities_.push_back({auxVar, payload.lhs, rhs, assertedLit});
    } else {
        activeAtoms_.push_back({atom.exprId, auxVar, payload.rel, value, payload.lhs, rhs, assertedLit});
    }
}

void LiaSolver::onBacktrack(int level) {
    currentLevel_ = level;
    repairModel_.reset();
    if (level == 0) {
        gs_.resetActiveBounds();
    } else {
        gs_.backtrackToLevel(level);
    }

    if (level == 0) {
        // Full reset for modelCheck rebuild or SAT restart to level 0.
        // All entries will be re-asserted by the caller.
        theoryTrail_.clear();
        trailIndexBySatVar_.clear();
        disequalities_.clear();
        activeAtoms_.clear();
        integerVars_.clear();   // incremental grow-only set: cleared on full reset
        interfaceEqualities_.clear();
        interfaceDisequalities_.clear();
    } else {
        while (!theoryTrail_.empty() && theoryTrail_.back().level > level) {
            const auto& e = theoryTrail_.back();
            if (e.isDiseq) {
                auto it = std::remove_if(disequalities_.begin(), disequalities_.end(),
                    [&e](const auto& d) { return d.lit == e.lit; });
                disequalities_.erase(it, disequalities_.end());
            } else {
                auto it = std::remove_if(activeAtoms_.begin(), activeAtoms_.end(),
                    [&e](const auto& a) { return a.lit == e.lit; });
                activeAtoms_.erase(it, activeAtoms_.end());
            }
            trailIndexBySatVar_.erase(e.atom.satVar);
            theoryTrail_.pop_back();
        }
        auto ieIt = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
            [level](const auto& ie) { return ie.level > level; });
        interfaceEqualities_.erase(ieIt, interfaceEqualities_.end());

        auto idIt = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
            [level](const auto& ie) { return ie.level > level; });
        interfaceDisequalities_.erase(idIt, interfaceDisequalities_.end());
    }
    if (appliedCursor_ > theoryTrail_.size()) {
        appliedCursor_ = theoryTrail_.size();
    }
    clearEntailmentDedupForBacktrack(level);
}

std::optional<TheoryCheckResult> LiaSolver::stageCore(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    pendingConflict_.reset();
    repairModel_.reset();

#ifdef XOLVER_LIA_PROFILE
    profile_.checkCalls++;
    int currentActive = static_cast<int>(theoryTrail_.size() + interfaceEqualities_.size() + interfaceDisequalities_.size());
    profile_.totalActiveLiterals += currentActive;
    if (currentActive > profile_.maxActiveLiterals) profile_.maxActiveLiterals = currentActive;
    profile_.totalNewLiterals += std::max(0, currentActive - profile_.prevActiveCount);
    profile_.prevActiveCount = currentActive;
    auto prof_t0 = std::chrono::steady_clock::now();
#endif

    if (!incrementalEnabled_) {
        // ---------------------------------------------------------------------
        // Full-rebuild mode (default, safe baseline): reset all bounds and
        // re-assert the entire theory trail every check.
        // ---------------------------------------------------------------------
        gs_.resetActiveBounds();
        disequalities_.clear();
        activeAtoms_.clear();
        integerVars_.clear();

        for (const auto& e : theoryTrail_) {
            const auto& payload = std::get<LinearAtomPayload>(e.atom.payload);

            for (const auto& [name, coeff] : payload.lhs.terms) {
                (void)coeff;
                int v = manager_.getOrCreateVar(gs_, name);
                integerVars_.insert(v);
            }

            if (e.isDiseq) {
                disequalities_.push_back({e.auxVar, payload.lhs, payload.rhs.asRational(), e.lit});
            } else {
                bool ok = manager_.assertBound(gs_, e.auxVar, payload.rel, e.value, e.lit, e.level,
                                               isIntegerLinearForm(payload));
                if (!ok) {
                    pendingConflict_ = PendingConflict{e.level, manager_.translateConflict(gs_)};
                    break;
                }
                activeAtoms_.push_back({e.atom.exprId, e.auxVar, payload.rel, e.value, payload.lhs, payload.rhs.asRational(), e.lit});
            }
        }
    } else {
        // ---------------------------------------------------------------------
        // Incremental replay (XOLVER_LIA_INCREMENTAL): apply only trail entries
        // not yet pushed to the simplex. activeAtoms_/disequalities_ are kept by
        // assertLit; gs_ push/pop + backtrackToLevel undo bounds on backtrack.
        // ---------------------------------------------------------------------
        while (appliedCursor_ < theoryTrail_.size()) {
            const auto& e = theoryTrail_[appliedCursor_];
            const auto& payload = std::get<LinearAtomPayload>(e.atom.payload);

            // Maintain integerVars_ incrementally: add this entry's variables as
            // it is applied, instead of rebuilding the whole set every check.
            // integerVars_ is grow-only between full resets (where it is cleared
            // — onReset / backtrack-to-0 / interface-diseq reset). A variable left
            // over from a backtracked atom is harmless: with no active bound it
            // takes an integer value and is never branched on.
            for (const auto& [name, coeff] : payload.lhs.terms) {
                (void)coeff;
                integerVars_.insert(manager_.getOrCreateVar(gs_, name));
            }

            if (!e.isDiseq) {
                bool ok = manager_.assertBound(gs_, e.auxVar, payload.rel, e.value, e.lit, e.level,
                                               isIntegerLinearForm(payload));
                if (!ok) {
                    pendingConflict_ = PendingConflict{e.level, manager_.translateConflict(gs_)};
                    break;
                }
            }

            ++appliedCursor_;
        }
    }

    if (pendingConflict_) {
#ifdef XOLVER_LIA_PROFILE
        auto prof_t1 = std::chrono::steady_clock::now();
        profile_.assertBoundTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t1 - prof_t0).count();
        int sz = static_cast<int>(pendingConflict_->conflict.clause.size());
        profile_.totalConflictSize += sz;
        if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
        profile_.immediateConflictCount++;
#endif
        bool ok = normalizeTheoryClause(pendingConflict_->conflict.clause);
        assert(ok && "complementary literal in pending conflict");
        (void)ok;
        dumpState("unsat_pending");
        return TheoryCheckResult::mkConflict(pendingConflict_->conflict);
    }

#ifdef XOLVER_LIA_PROFILE
    auto prof_t1 = std::chrono::steady_clock::now();
    profile_.assertBoundTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t1 - prof_t0).count();
    auto prof_t2 = prof_t1;
#endif

    // integerVars_ is maintained incrementally in the replay loop above
    // (incremental mode) or rebuilt inline in the full-rebuild branch.

    // Apply interface equalities from Nelson-Oppen combination
    for (const auto& ieq : interfaceEqualities_) {
        int aux = getOrCreateInterfaceEqAuxVar(ieq.a, ieq.b);
        if (aux >= 0) {
            bool ok = true;
            ok = gs_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0)), ieq.reason)) && ok;
            ok = gs_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0)), ieq.reason)) && ok;
            if (!ok) {
                auto tc = manager_.translateConflict(gs_);
                tc.clause.push_back(ieq.reason);
#ifdef XOLVER_LIA_PROFILE
                auto prof_t3 = std::chrono::steady_clock::now();
                profile_.assertBoundTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t3 - prof_t2).count();
                int sz = static_cast<int>(tc.clause.size());
                profile_.totalConflictSize += sz;
                if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
                profile_.immediateConflictCount++;
#endif
                bool ok = normalizeTheoryClause(tc.clause);
                assert(ok && "complementary literal in IEQ conflict");
                (void)ok;
                return TheoryCheckResult::mkConflict(std::move(tc));
            }
        }
    }

    auto r = gs_.check();

#ifdef XOLVER_LIA_PROFILE
    auto prof_t3 = std::chrono::steady_clock::now();
    profile_.simplexCheckTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t3 - prof_t2).count();
    profile_.totalPivotCount += gs_.pivotCount();
    gs_.resetPivotCount();
    auto cs = gs_.coeffStats();
    profile_.mpqOpTimeUs += cs.mpqOpTimeUs;
    profile_.maxCoeffNumBits = std::max(profile_.maxCoeffNumBits, cs.maxCoeffNumBits);
    profile_.maxCoeffDenBits = std::max(profile_.maxCoeffDenBits, cs.maxCoeffDenBits);
    profile_.totalCoeffNumBits += cs.totalCoeffNumBits;
    profile_.totalCoeffDenBits += cs.totalCoeffDenBits;
    profile_.totalCoeffSamples += cs.totalCoeffSamples;
    gs_.resetCoeffStats();
    auto prof_t4 = prof_t3;
#endif

    if (r == GeneralSimplex::Result::Unsat) {
        auto tc = TheoryConflict{};
        const auto& conflict = gs_.getConflict();
        if (!conflict.empty()) {
            for (const auto& cr : conflict) {
                tc.clause.push_back(cr.reason);
            }
#ifdef XOLVER_LIA_PROFILE
            int sz = static_cast<int>(tc.clause.size());
            profile_.totalConflictSize += sz;
            if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
            if (gs_.hasImmediateConflict()) {
                profile_.immediateConflictCount++;
            } else {
                profile_.rowConflictCount++;
            }
#endif
        } else {
            tc.clause = allActiveReasons();
#ifdef XOLVER_LIA_PROFILE
            int sz = static_cast<int>(tc.clause.size());
            profile_.totalConflictSize += sz;
            if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
            profile_.fallbackConflictCount++;
#endif
        }
        bool ok = normalizeTheoryClause(tc.clause);
        assert(ok && "complementary literal in simplex conflict");
        (void)ok;
        return TheoryCheckResult::mkConflict(std::move(tc));
    }
    if (r == GeneralSimplex::Result::Unknown) {
        return TheoryCheckResult::unknown();
    }

    // P3: Check interface disequalities. LIA is non-convex; if any
    // interface disequality is provably fixed to 0, we cannot
    // emit a split lemma without arrangement. Return Unknown conservatively.
    // But if aux is not fixed (free variable), LIA has no opinion — let EUF handle it.
    for (const auto& ieq : interfaceDisequalities_) {
        // Direct entailment: an asserted 2-var equality (e.g. (+i1)=(+j1) ⟺
        // i - j = 0) makes i = j, so an interface disequality i != j is a hard
        // conflict. The conflict clause is {asserted-eq-lit, diseq-reason}
        // (both currently true). Caught here before the conservative
        // fixed-value Unknown gate below, turning R4 into a real UNSAT.
        if (auto eqReasons = assertedVarEqualityReason(ieq.a, ieq.b); !eqReasons.empty()) {
            TheoryConflict tc;
            for (auto l : eqReasons) tc.clause.push_back(l);
            tc.clause.push_back(ieq.reason);
            if (normalizeTheoryClause(tc.clause)) {
                return TheoryCheckResult::mkConflict(std::move(tc));
            }
        }
        int aux = getOrCreateInterfaceEqAuxVar(ieq.a, ieq.b);
        if (aux >= 0) {
            auto fixedOpt = gs_.proveFixedValue(aux);
            if (fixedOpt && fixedOpt->first.isZero()) {
                // The difference x - y is provably pinned to 0 by bounds (e.g.
                // x<=y ∧ y<=x), so x = y is entailed and the interface
                // disequality x != y is a hard conflict. Build the conflict
                // from the pinning bound reasons + the disequality reason
                // (proof-carrying), instead of the old conservative Unknown.
                TheoryConflict tc;
                for (const auto& br : fixedOpt->second) tc.clause.push_back(br.reason);
                tc.clause.push_back(ieq.reason);
                if (normalizeTheoryClause(tc.clause)) {
                    return TheoryCheckResult::mkConflict(std::move(tc));
                }
                // Defensive: if the conflict cannot be normalized (a
                // complementary pair slipped in), fall back to the previous
                // sound-but-incomplete Unknown.
                return TheoryCheckResult::unknown();
            }
            // Track B fix (LIA): when proveFixedValue misses (Wisa class), try
            // the LP-duality probe — true multi-row Farkas via feasibility
            // query. Same RAII/marker discipline as LRA. Without this, SAT can
            // satisfy by deciding the deduced eq atom FALSE and LIA would
            // silently accept the diseq under a polyhedron that actually
            // entails equality.
            //
            // GATED by XOLVER_LIA_LP_DUALITY (default OFF): the synthetic
            // alia_012 case regressed from sat to unknown when this fired
            // unconditionally — likely an integer-vs-LP interaction (the
            // simplex relaxation pins what integer reasoning doesn't, and our
            // probe over-fires in the LIA context). Keep the LRA Track B fix
            // ON (it recovers pos_pinbounds without regressions); guard the
            // LIA mirror behind a separate flag until the integer/LP edge is
            // understood and the alia_012 class re-passes.
            static const bool liaProbeOk = xolver::env::diag("XOLVER_LIA_LP_DUALITY");
            // Gate: skip the LIA LP-duality probe entirely when arrays are in
            // play. ROOT CAUSE: GeneralSimplex::push/pop only restores the
            // bound trail; the probe's internal check() can pivot the tableau,
            // and those pivots persist past pop. The resulting tableau gives
            // LIA's downstream model construction a different integer model
            // that the array soundness gate then correctly rejects as
            // "missed array axiom instance" — alia_012 transitions from sat
            // to unknown. The two clean fixes are (a) snapshot+restore the
            // full simplex state in ProbeScope (heavy), or (b) skip the probe
            // when array-sort shared terms exist (cheap, narrow). Choosing
            // (b) until (a) is justified by recovery numbers it would unlock.
            // Pre-filter on current value also skips when polyhedron doesn't
            // pin (probe would be Sat both directions = waste).
            bool hasArrayShared = false;
            if (liaProbeOk && impliedEqEnabled_ && !fixedOpt &&
                sharedTermRegistry_ && sharedTermRegistry_->coreIr()) {
                const CoreIr* ir = sharedTermRegistry_->coreIr();
                for (SharedTermId st : sharedTermRegistry_->allSharedTerms()) {
                    if (const auto* s = sharedTermRegistry_->get(st)) {
                        if (ir->arraySortParams(s->sort)) {
                            hasArrayShared = true;
                            break;
                        }
                    }
                }
            }
            if (liaProbeOk && impliedEqEnabled_ && !fixedOpt && !hasArrayShared) {
                DeltaRational cur = gs_.value(aux);
                bool prefilterOk = (cur.a == 0 && cur.b == 0);
                std::vector<SatLit> probeReasons;
                bool pinned = false;
                if (prefilterOk) pinned = tryProvePairEqualityByLpDuality(aux, probeReasons);
                if (pinned) {
                    TheoryConflict tc;
                    for (auto l : probeReasons) tc.clause.push_back(l);
                    tc.clause.push_back(ieq.reason);
                    if (normalizeTheoryClause(tc.clause)) {
                        return TheoryCheckResult::mkConflict(std::move(tc));
                    }
                }
            }
            // Honor a DECIDED interface disequality the convex model violates:
            // (a != b) decided but the simplex point happens to set a = b
            // (both free -> defaulted equal). Branch the integer model apart:
            //   (a != b) => (a - b <= -1) OR (a - b >= 1).
            // Only at Full effort (a real model is in hand) and only when both
            // shared terms resolve to simplex variables.
            SharedTermId loK = ieq.a < ieq.b ? ieq.a : ieq.b;
            SharedTermId hiK = ieq.a < ieq.b ? ieq.b : ieq.a;
            uint64_t authKey = (static_cast<uint64_t>(loK) << 32) |
                               static_cast<uint64_t>(hiK);
            if (effort == TheoryEffort::Full && registry_ &&
                !fixedOpt && diseqBranchAuthorized_.count(authKey)) {
                std::string va = getVarNameForSharedTerm(ieq.a);
                std::string vb = getVarNameForSharedTerm(ieq.b);
                if (!va.empty() && !vb.empty() && va != vb &&
                    va.rfind("__const_", 0) != 0 && vb.rfind("__const_", 0) != 0) {
                    DeltaRational d = gs_.value(aux);
                    if (d.a == 0 && d.b == 0) {
                        LinearFormKey form;
                        form.terms.push_back({va, mpq_class(1)});
                        form.terms.push_back({vb, mpq_class(-1)});
                        SatLit litLe = registry_->getOrCreateLinearBoundAtom(
                            form, Relation::Leq, mpq_class(-1), TheoryId::LIA);
                        SatLit litGe = registry_->getOrCreateLinearBoundAtom(
                            form, Relation::Geq, mpq_class(1), TheoryId::LIA);
                        TheoryLemma lemma{{ieq.reason.negated(), litLe, litGe}};
                        if (!lemmaDb.contains(lemma)) {
                            return TheoryCheckResult::mkLemma(std::move(lemma));
                        }
                    }
                }
            }
        }
    }

    if (!ultraSafeMode_) {
        // Only handle disequalities at Full effort (model check).
        // At Standard effort (cb_propagate), partial assignments may not
        // give enough information for proveFixedValue, and split lemmas
        // cannot be propagated anyway (cb_propagate ignores lemmas).
        // This avoids useless work and prevents memory corruption bugs
        // triggered by repeated split-lemma generation in propagate.
        if (effort == TheoryEffort::Full && !disequalities_.empty()) {
            auto dr = handleDisequalities(lemmaDb);
            if (dr.kind != TheoryCheckResult::Kind::Consistent) {
#ifdef XOLVER_LIA_PROFILE
                if (dr.kind == TheoryCheckResult::Kind::Lemma) {
                    profile_.disequalitySplitCount++;
                }
#endif
                return dr;
            }
        }
    }

    // Integer-Diophantine tightening (arith-dio-tighten) — refute unbounded
    // Diophantine systems BEFORE branch-and-bound thrashes on the unbounded
    // mod-lowering quotient vars. Full effort only (the assignment is complete,
    // so the disequalities that drive the refutation are decided).
    if (dioTightenEnabled_ && effort == TheoryEffort::Full && !disequalities_.empty()) {
        if (auto dc = checkDioTighten()) {
            if (normalizeTheoryClause(dc->clause))
                return TheoryCheckResult::mkConflict(std::move(*dc));
        }
    }

    auto ir = ultraSafeMode_ ? TheoryCheckResult::consistent() : checkIntegrality(lemmaDb, effort);

#ifdef XOLVER_LIA_PROFILE
    auto prof_t5 = std::chrono::steady_clock::now();
    profile_.integralityCheckTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t5 - prof_t4).count();
    if (ir.kind == TheoryCheckResult::Kind::Lemma) {
        profile_.branchSplitCount++;
    }
#endif
    if (ir.kind == TheoryCheckResult::Kind::Consistent) {
        // A successful rounding repair (XOLVER_LIA_REPAIR) has already
        // exact-validated its integer point against every active atom and
        // disequality, and stored it in repairModel_. The simplex β still holds
        // the fractional relaxation, so the gs_-based validator below would
        // (correctly) reject it — skip it and report SAT via the repaired model.
        if (repairModel_) {
            dumpState("sat_repair");
            return TheoryCheckResult::consistent();
        }
        std::vector<DiseqValidationInfo> diseqInfos;
        for (const auto& d : disequalities_) {
            diseqInfos.push_back({d.auxVar});
        }
        if (!validator_.validateLiaModel(activeAtoms_, diseqInfos, integerVars_, gs_)) {
            dumpState("sat_validator_failed");
            return TheoryCheckResult::unknown();
        }
        dumpState("sat");
        return TheoryCheckResult::consistent();
    }

    if (!ultraSafeMode_ && !activeAtoms_.empty()) {
        auto cr = integerReasoner_.run(activeAtoms_);
        if (cr) {
            if (cr->kind == TheoryCheckResult::Kind::Lemma && cr->lemmaOpt) {
                if (!lemmaDb.contains(*cr->lemmaOpt)) return *cr;
            } else {
                return *cr;
            }
        }
    }

    if (ir.kind == TheoryCheckResult::Kind::Lemma && ir.lemmaOpt) {
        if (!lemmaDb.contains(*ir.lemmaOpt)) {
            return ir;
        }
    }

    return TheoryCheckResult::unknown();
}


// ---------------------------------------------------------------------------
// XOLVER_LIA_REPAIR: rounding-based integrality repair
// ---------------------------------------------------------------------------

// roundNearest() moved to LiaSolverDetail.h (round half-up to nearest integer),
// shared across the split LiaSolver_*.cpp translation units.


// ---------------------------------------------------------------------------
// XOLVER_LIA_CUTS: Gomory fractional cuts
// ---------------------------------------------------------------------------


// ---------------------------------------------------------------------------
// Nelson-Oppen combination hooks (experimental skeleton for non-convex LIA)
// ---------------------------------------------------------------------------

// getVarNameForSharedTerm hoisted to ArithSolverBase (2026-06-04).


// ============================================================================
// Debug dump helpers
// ============================================================================


// ---------------------------------------------------------------------------
// Entailment propagation
// ---------------------------------------------------------------------------


} // namespace xolver
