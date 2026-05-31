#include "util/MpqUtils.h"
#include "theory/arith/lia/LiaSolver.h"
#include "util/MpqUtils.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/arith/Reasoner.h"
#include "theory/arith/linear/SimplexDiseqSplitter.h"
#include "theory/arith/lia/GomoryCut.h"
#include <cassert>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <filesystem>
#include <cstdlib>
#include <sstream>
#include <map>

namespace xolver {

// True if the atom's linear form is integer-valued (integer coefficients and
// integer rhs). In LiaSolver every variable is an integer, so the aux var
// s = Σ coeff·x − rhs is then integer too, enabling exact strict→±1 tightening.
static bool isIntegerLinearForm(const LinearAtomPayload& p) {
    if (!p.rhs.isRational() || p.rhs.asRational().get_den() != 1) return false;
    for (const auto& t : p.lhs.terms) {
        if (t.second.get_den() != 1) return false;
    }
    return true;
}

LiaSolver::LiaSolver() {
    const char* env = std::getenv("XOLVER_LIA_DUMP_DIR");
    if (env) {
        dumpCounter_ = 0;
    }
    const char* repairEnv = std::getenv("XOLVER_LIA_REPAIR");
    repairEnabled_ = (repairEnv && *repairEnv && *repairEnv != '0');
    const char* cutsEnv = std::getenv("XOLVER_LIA_CUTS");
    cutsEnabled_ = (cutsEnv && *cutsEnv && *cutsEnv != '0');
    const char* gmiEnv = std::getenv("XOLVER_LIA_GMI_CUTS");
    gmiCutsEnabled_ = (gmiEnv && *gmiEnv && *gmiEnv != '0');
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
    const char* incEnv = std::getenv("XOLVER_LIA_INCREMENTAL");
    incrementalEnabled_ = (incEnv && *incEnv && *incEnv != '0');
    const char* impl = std::getenv("XOLVER_SIMPLEX_IMPLIED_EQ");
    impliedEqEnabled_ = (impl && *impl && *impl != '0');
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
    appliedCursor_ = 0;
    activeAtoms_.clear();
    disequalities_.clear();
    pendingConflict_.reset();
    diseqBranchAuthorized_.clear();
    repairModel_.reset();
    cutsThisSolve_ = 0;
    gs_.resetActiveBounds();
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

    for (auto& e : theoryTrail_) {
        if (e.atom.satVar == atom.satVar) {
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
    }
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
        disequalities_.clear();
        activeAtoms_.clear();
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

    if (incrementalEnabled_) {
        // Rebuild integerVars_ from activeAtoms_ and disequalities_ (the
        // full-rebuild branch builds it inline; incremental did not touch it).
        integerVars_.clear();
        for (const auto& a : activeAtoms_) {
            for (const auto& [name, coeff] : a.lhs.terms) {
                (void)coeff;
                int v = manager_.getOrCreateVar(gs_, name);
                integerVars_.insert(v);
            }
        }
        for (const auto& d : disequalities_) {
            for (const auto& [name, coeff] : d.lhs.terms) {
                (void)coeff;
                int v = manager_.getOrCreateVar(gs_, name);
                integerVars_.insert(v);
            }
        }
    }

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
            static const bool liaProbeOk = std::getenv("XOLVER_LIA_LP_DUALITY") != nullptr;
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

TheoryCheckResult LiaSolver::handleDisequalities(TheoryLemmaStorage& lemmaDb) {
    return handleSimplexDisequalities(
        disequalities_, gs_, lemmaDb,
        [this](const DiseqInfo& d) -> TheoryCheckResult {
            // If the disequality is forced to be false by current bounds
            // (auxVar is fixed to 0), return a precise conflict.
            auto val = gs_.value(d.auxVar);
            auto proved = gs_.proveFixedValue(d.auxVar);
            if (proved && proved->first.isZero()) {
                TheoryConflict tc;
                for (const auto& br : proved->second) {
                    tc.clause.push_back(br.reason);
                }
                tc.clause.push_back(d.lit);
                bool ok = normalizeTheoryClause(tc.clause);
                assert(ok && "complementary literal in disequality conflict");
                (void)ok;
                return TheoryCheckResult::mkConflict(std::move(tc));
            }

            if (d.rhs.get_den() != 1) {
                return TheoryCheckResult::consistent();
            }

            mpz_class g = 0;
            for (const auto& t : d.lhs.terms) {
                const mpq_class& c = t.second;
                if (c.get_den() != 1) {
                    g = 1;
                    break;
                }
                mpz_class a = c.get_num();
                if (a < 0) a = -a;
                if (a == 0) continue;
                if (g == 0) {
                    g = a;
                } else {
                    mpz_class tmp;
                    mpz_gcd(tmp.get_mpz_t(), g.get_mpz_t(), a.get_mpz_t());
                    g = tmp;
                }
            }

            mpz_class c = d.rhs.get_num();

            if (g == 0) {
                if (c == 0) {
                    auto tc = TheoryConflict{{d.lit}};
                    bool ok = normalizeTheoryClause(tc.clause);
                    assert(ok && "complementary literal in gcd conflict");
                    (void)ok;
                    return TheoryCheckResult::mkConflict(std::move(tc));
                }
                return TheoryCheckResult::consistent();
            }

            if (c % g != 0) {
                return TheoryCheckResult::consistent();
            }

            assert(registry_ != nullptr);
            mpq_class leRhs = mpq_class(c - g, 1);
            mpq_class geRhs = mpq_class(c + g, 1);

            auto lit1 = registry_->getOrCreateLinearBoundAtom(
                d.lhs, Relation::Leq, leRhs, TheoryId::LIA);
            auto lit2 = registry_->getOrCreateLinearBoundAtom(
                d.lhs, Relation::Geq, geRhs, TheoryId::LIA);

            return TheoryCheckResult::mkLemma(
                TheoryLemma{{d.lit.negated(), lit1, lit2}});
        });
}

TheoryCheckResult LiaSolver::checkIntegrality(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    // Cap Gomory cuts per solve so branch-and-bound still terminates AND the
    // tableau doesn't bloat into degeneracy (too many near-degenerate cut rows
    // make the anti-cycling pivot rule blow past the iteration cap -> unknown,
    // the CAV coef-size regression).
    //
    // Default 4 ("cut-and-branch"): measured on the QF_LIA panda regressors
    // (dillig 25-*/45-*, Bromberger *.slack), every cut a fractional SAT node
    // generates perturbs the branching search and mints a fresh bound atom that
    // enlarges the boolean search — on SAT instances cuts are pure overhead and
    // the old default of 32 turned 16-20s base solves into >30s timeouts. A
    // small budget concentrates cuts near the root (where they tighten the
    // initial relaxation, helping UNSAT) and then lets branch-and-bound run
    // undisturbed. Tunable via XOLVER_LIA_CUT_MAXPERSOLVE; raise it for
    // UNSAT-heavy divisions if a differential shows more root cuts help there.
    static const int kMaxCutsPerSolve = []() {
        const char* e = std::getenv("XOLVER_LIA_CUT_MAXPERSOLVE");
        int v = e ? std::atoi(e) : -1;
        return v >= 0 ? v : 4;
    }();
    int bestVar = -1;
    mpq_class bestFrac(-1);

    for (int v : integerVars_) {
        auto val = gs_.value(v);
        if (val.b != 0 || val.a.get_den() != 1) {
            mpq_class frac;
            if (val.b != 0) {
                // Delta-rational: value is a + b·δ where δ is infinitesimal.
                // If b > 0, value is just above a (frac ≈ 1).
                // If b < 0, value is just below a (frac ≈ 0).
                // Use 1/2 as a representative fractional distance.
                frac = mpq_class(1, 2);
            } else {
                // Compute fractional part = |val.a - floor(val.a)|
                mpz_class num = val.a.get_num();
                mpz_class den = val.a.get_den();
                mpz_class f = num / den;  // truncates toward zero
                mpz_class r = num % den;
                mpz_class floorVal;
                if (r == 0) {
                    floorVal = f;
                } else if (num >= 0) {
                    floorVal = f;
                } else {
                    floorVal = f - 1;
                }
                frac = val.a - mpq_class(floorVal, 1);
                if (frac < 0) frac = -frac;
            }
            if (frac > bestFrac) {
                bestFrac = frac;
                bestVar = v;
            }
        }
    }

    if (bestVar != -1) {
        // XOLVER_LIA_REPAIR: before splitting, try to round the LRA relaxation
        // to a nearby integer point and exact-validate it. Only at Full effort
        // (a real, complete relaxation model is in hand). A success short-cuts
        // potentially deep branch-and-bound to an immediate SAT.
        // Soundness gate: repair validates only the LIA atoms + disequalities,
        // NOT Nelson-Oppen interface (dis)equalities. In a combined logic a
        // rounded point could violate an asserted x=y and produce a wrong SAT,
        // so repair only fires when no interface constraints are active (always
        // the case in pure QF_LIA).
        if (repairEnabled_ && effort == TheoryEffort::Full &&
            interfaceEqualities_.empty() && interfaceDisequalities_.empty() &&
            tryIntegralityRepair()) {
            return TheoryCheckResult::consistent();
        }
        // XOLVER_LIA_CUTS / XOLVER_LIA_GMI_CUTS: try a Gomory (or GMI) cut before
        // splitting. A cut tightens the relaxation without branching; capped per
        // solve so branch-and-bound still terminates. Only at Full effort (a real
        // model). GMI implies the cut path so it can be enabled standalone.
        if ((cutsEnabled_ || gmiCutsEnabled_) && effort == TheoryEffort::Full &&
            cutsThisSolve_ < kMaxCutsPerSolve) {
            if (auto cut = generateGomoryCut(bestVar)) {
                if (!lemmaDb.contains(*cut)) {
                    ++cutsThisSolve_;
                    return TheoryCheckResult::mkLemma(std::move(*cut));
                }
            }
        }
        assert(registry_ != nullptr);
        return TheoryCheckResult::mkLemma(buildBranchSplitLemma(bestVar, gs_.value(bestVar)));
    }
    return TheoryCheckResult::consistent();
}

// ---------------------------------------------------------------------------
// XOLVER_LIA_REPAIR: rounding-based integrality repair
// ---------------------------------------------------------------------------

// floor(q + 1/2): round half-up to the nearest integer.
static mpz_class roundNearest(const mpq_class& q) {
    mpq_class h = q + mpq_class(1, 2);
    mpz_class r;
    mpz_fdiv_q(r.get_mpz_t(), h.get_num().get_mpz_t(), h.get_den().get_mpz_t());
    return r;
}

bool LiaSolver::pointSatisfiesAll(
    const std::unordered_map<std::string, mpq_class>& pt) const {
    auto eval = [&](const LinearFormKey& lhs, mpq_class& out) -> bool {
        out = 0;
        for (const auto& [name, coeff] : lhs.terms) {
            auto it = pt.find(name);
            if (it == pt.end()) return false;  // value unknown -> cannot validate
            out += coeff * it->second;
        }
        return true;
    };
    for (const auto& a : activeAtoms_) {
        mpq_class f;
        if (!eval(a.lhs, f)) return false;
        Relation rel = a.value ? a.rel : negateRelation(a.rel);
        bool ok;
        switch (rel) {
            case Relation::Eq:  ok = (f == a.rhs); break;
            case Relation::Neq: ok = (f != a.rhs); break;
            case Relation::Lt:  ok = (f <  a.rhs); break;
            case Relation::Leq: ok = (f <= a.rhs); break;
            case Relation::Gt:  ok = (f >  a.rhs); break;
            case Relation::Geq: ok = (f >= a.rhs); break;
            default:            ok = false; break;
        }
        if (!ok) return false;
    }
    for (const auto& d : disequalities_) {
        mpq_class f;
        if (!eval(d.lhs, f)) return false;
        if (f == d.rhs) return false;  // disequality violated
    }
    return true;
}

bool LiaSolver::tryIntegralityRepair() {
    // Collect (name, floor, ceil, nearest) for every original integer variable.
    struct VarRound {
        std::string name;
        mpq_class lo, hi, nearest;
    };
    std::vector<VarRound> vr;
    vr.reserve(integerVars_.size());
    for (int v : integerVars_) {
        std::string name = manager_.getVarName(v);
        if (name.empty()) continue;            // aux/slack vars are determined
        const mpq_class& a = gs_.value(v).a;
        mpz_class fl, cl;
        mpz_fdiv_q(fl.get_mpz_t(), a.get_num().get_mpz_t(), a.get_den().get_mpz_t());
        mpz_cdiv_q(cl.get_mpz_t(), a.get_num().get_mpz_t(), a.get_den().get_mpz_t());
        vr.push_back({name, mpq_class(fl), mpq_class(cl), mpq_class(roundNearest(a))});
    }
    if (vr.empty()) return false;

    auto tryPoint = [&](const std::unordered_map<std::string, mpq_class>& pt) -> bool {
        if (!pointSatisfiesAll(pt)) return false;
        repairModel_ = pt;
        return true;
    };
    auto buildUniform = [&](int which) {  // 0=nearest, 1=floor, 2=ceil
        std::unordered_map<std::string, mpq_class> pt;
        pt.reserve(vr.size());
        for (const auto& r : vr) pt[r.name] = (which == 1 ? r.lo : which == 2 ? r.hi : r.nearest);
        return pt;
    };

    bool ok = false;
    // 1) Round-to-nearest, then the all-floor / all-ceil corners.
    if (tryPoint(buildUniform(0)) || tryPoint(buildUniform(1)) || tryPoint(buildUniform(2))) {
        ok = true;
    } else {
        // 2) One-variable flip neighbourhood around the nearest point: flip each
        //    single variable to its other neighbour (floor<->ceil). Bounded by
        //    #vars, catches the common "one coordinate rounded the wrong way".
        auto base = buildUniform(0);
        for (const auto& r : vr) {
            mpq_class other = (base[r.name] == r.lo) ? r.hi : r.lo;
            if (other == base[r.name]) continue;  // already integral
            mpq_class saved = base[r.name];
            base[r.name] = other;
            if (tryPoint(base)) { ok = true; break; }
            base[r.name] = saved;
        }
    }
    return ok;
}

// ---------------------------------------------------------------------------
// XOLVER_LIA_CUTS: Gomory fractional cuts
// ---------------------------------------------------------------------------

bool LiaSolver::isSimplexVarInteger(int idx) const {
    std::string nm = manager_.getVarName(idx);
    if (!nm.empty()) {
        // Original variable: integer iff registered as an integer variable.
        return integerVars_.count(idx) > 0;
    }
    // Auxiliary variable s = Σ c_k * v_k - rhs: integer iff every c_k and rhs
    // are integers and every v_k is an integer variable.
    LinearFormKey form;
    mpq_class auxRhs;
    if (!manager_.auxForm(idx, form, auxRhs)) return false;
    if (auxRhs.get_den() != 1) return false;
    for (const auto& [vn, c] : form.terms) {
        if (c.get_den() != 1) return false;
        int vi = manager_.findVarIndex(vn);
        if (vi < 0 || integerVars_.count(vi) == 0) return false;
    }
    return true;
}

std::optional<TheoryLemma> LiaSolver::generateGomoryCut(int xi) {
    if (!registry_) return std::nullopt;
    if (!gs_.isBasic(xi)) return std::nullopt;     // need a tableau row
    int r = gs_.basicRowOfVar(xi);
    const SparseRow& row = gs_.tableau().row(r);

    DeltaRational beta = gs_.value(xi);
    if (beta.b != 0) return std::nullopt;          // delta-valued: skip
    mpq_class f0 = gmiFractionalPart(beta.a);
    if (f0 == 0) return std::nullopt;              // not actually fractional

    // x_i = beta_i + Σ_j chat_j y_j, y_j = (x_j - bound_j), each nonbasic at a
    // bound. chat_j = +a_ij at lower, -a_ij at upper.
    struct NbInfo { int var; bool atLower; mpq_class bound; SatLit reason; };
    std::vector<GmiNonbasicTerm> terms;
    std::vector<NbInfo> nb;
    for (const auto& e : row.entries) {
        int xj = e.col;
        const mpq_class& aij = e.coeff;
        if (aij == 0) continue;
        auto st = gs_.varState(xj);
        DeltaRational vj = gs_.value(xj);
        bool atLower = st.lower.bound.isFinite() && vj == st.lower.bound.value;
        bool atUpper = !atLower && st.upper.bound.isFinite() && vj == st.upper.bound.value;
        if (!atLower && !atUpper) return std::nullopt;       // free nonbasic: no y >= 0
        const BoundInfo& bi = atLower ? st.lower : st.upper;
        if (bi.bound.value.b != 0) return std::nullopt;      // strict/delta bound: skip
        if (!bi.reason.has_value()) return std::nullopt;     // need reason for explanation
        mpq_class boundVal = bi.bound.value.a;
        mpq_class chat = atLower ? aij : -aij;
        bool yInt = isSimplexVarInteger(xj) && (boundVal.get_den() == 1);
        terms.push_back({chat, yInt});
        nb.push_back({xj, atLower, boundVal, *bi.reason});
    }
    if (terms.empty()) return std::nullopt;

    // GMI (XOLVER_LIA_GMI_CUTS) folds continuous nonbasics into the cut instead
    // of bailing; the pure fractional cut requires every term integer. Both
    // return the same {gamma>=0, rhs>0} shape, so the back-substitution below is
    // shared. The coefficient bit-cap further down rejects any blown-up cut
    // (GMI's f0/(1-f0) factor can compound rationals) so the exact simplex never
    // bogs down.
    auto cutOpt = gmiCutsEnabled_ ? deriveGmiCut(f0, terms)
                                  : deriveGomoryCut(f0, terms);
    if (!cutOpt) return std::nullopt;              // non-integer term / vacuous

    // Re-express Σ gamma_j y_j >= R over original variables:
    //   Σ tau_j x_j >= R + Σ tau_j bound_j (+ aux form-constant adjustment),
    //   tau_j = +gamma_j (at lower) / -gamma_j (at upper).
    std::unordered_map<std::string, mpq_class> coeff;
    mpq_class rhsFinal = cutOpt->rhs;
    std::vector<SatLit> reasons;
    for (size_t j = 0; j < nb.size(); ++j) {
        const mpq_class& gamma = cutOpt->gamma[j];
        if (gamma == 0) continue;                  // absent term: bound not needed
        mpq_class tau = nb[j].atLower ? gamma : mpq_class(-gamma);
        rhsFinal += tau * nb[j].bound;
        std::string nm = manager_.getVarName(nb[j].var);
        if (!nm.empty()) {
            coeff[nm] += tau;
        } else {
            LinearFormKey form;
            mpq_class auxRhs;
            if (!manager_.auxForm(nb[j].var, form, auxRhs)) return std::nullopt;
            for (const auto& [vn, c] : form.terms) coeff[vn] += tau * c;
            rhsFinal += tau * auxRhs;
        }
        reasons.push_back(nb[j].reason);
    }

    LinearFormKey cutForm;
    for (const auto& [vn, c] : coeff) if (c != 0) cutForm.terms.push_back({vn, c});
    if (cutForm.terms.empty()) return std::nullopt;  // degenerate constant cut
    std::sort(cutForm.terms.begin(), cutForm.terms.end(),
              [](const auto& a, const auto& b) { return a.first < b.first; });

    // Cut-coefficient size cap: reject blown-up cuts. On large-coefficient
    // instances (CAV coef-size) the Gomory fractional parts compound into huge
    // rationals; such cuts bog down the exact-rational simplex (it hits its
    // iteration cap -> unknown) without improving the bound. Rejecting them lets
    // the solver fall back to branching, which is fast. Tunable for A/B.
    {
        static const int kMaxBits = []() {
            const char* e = std::getenv("XOLVER_LIA_CUT_MAXBITS");
            int v = e ? std::atoi(e) : 0;
            return v > 0 ? v : 8;
        }();
        auto bits = [](const mpq_class& q) -> size_t {
            return std::max(mpz_sizeinbase(q.get_num().get_mpz_t(), 2),
                            mpz_sizeinbase(q.get_den().get_mpz_t(), 2));
        };
        size_t mx = bits(rhsFinal);
        for (const auto& [vn, c] : cutForm.terms) mx = std::max(mx, bits(c));
        if (mx > static_cast<size_t>(kMaxBits)) return std::nullopt;
    }

    SatLit cutLit = registry_->getOrCreateLinearBoundAtom(
        cutForm, Relation::Geq, rhsFinal, TheoryId::LIA);

    // Explanation-aware lemma: (Σ reasons) -> cut, i.e. clause {¬reasons, cutLit}.
    std::vector<SatLit> clause;
    clause.reserve(reasons.size() + 1);
    for (SatLit rr : reasons) clause.push_back(rr.negated());
    clause.push_back(cutLit);
    std::sort(clause.begin(), clause.end(), [](SatLit a, SatLit b) {
        return a.var < b.var || (a.var == b.var && a.sign < b.sign);
    });
    clause.erase(std::unique(clause.begin(), clause.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), clause.end());
    return TheoryLemma{clause};
}

TheoryLemma LiaSolver::buildBranchSplitLemma(int var, const DeltaRational& val) {
    mpq_class q = val.a;
    mpz_class num = q.get_num();
    mpz_class den = q.get_den();

    mpq_class floorVal;
    mpq_class ceilVal;

    if (den == 1) {
        if (val.b > 0) {
            // value = a + epsilon, strictly greater than a
            floorVal = q;
            ceilVal = mpq_class(num + 1, 1);
        } else if (val.b < 0) {
            // value = a - epsilon, strictly less than a
            floorVal = mpq_class(num - 1, 1);
            ceilVal = q;
        } else {
            floorVal = q;
            ceilVal = q;
        }
    } else {
        mpz_class f = num / den;
        mpz_class r = num % den;
        if (r == 0) {
            floorVal = mpq_class(f, 1);
            ceilVal = mpq_class(f, 1);
        } else if (num >= 0) {
            floorVal = mpq_class(f, 1);
            ceilVal = mpq_class(f + 1, 1);
        } else {
            floorVal = mpq_class(f - 1, 1);
            ceilVal = mpq_class(f, 1);
        }
    }

    std::string name = manager_.getVarName(var);
    if (name.empty()) {
        return TheoryLemma{};
    }

    LinearFormKey form;
    form.terms.push_back({name, mpq_class(1)});

    auto litLo = registry_->getOrCreateLinearBoundAtom(form, Relation::Leq, floorVal, TheoryId::LIA);
    auto litHi = registry_->getOrCreateLinearBoundAtom(form, Relation::Geq, ceilVal, TheoryId::LIA);

    return TheoryLemma{{litLo, litHi}};
}

// ---------------------------------------------------------------------------
// Nelson-Oppen combination hooks (experimental skeleton for non-convex LIA)
// ---------------------------------------------------------------------------

std::string LiaSolver::getVarNameForSharedTerm(SharedTermId s) {
    auto it = sharedTermToVarName_.find(s);
    if (it != sharedTermToVarName_.end()) return it->second;

    if (!sharedTermRegistry_ || !coreIr_) return "";
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return "";

    const auto& expr = coreIr_->get(st->coreExpr);
    std::string name;
    if (expr.kind == Kind::Variable) {
        if (std::holds_alternative<std::string>(expr.payload.value)) {
            name = std::get<std::string>(expr.payload.value);
        }
    } else if (expr.isConst()) {
        // Constants participate in interface equalities via a synthetic variable.
        // The actual constant value is enforced via bound assertion in check().
        name = "__const_" + st->name;
    }
    if (!name.empty()) {
        sharedTermToVarName_[s] = name;
    }
    return name;
}

int LiaSolver::getOrCreateInterfaceEqAuxVar(SharedTermId a, SharedTermId b) {
    SharedTermId lo = a < b ? a : b;
    SharedTermId hi = a < b ? b : a;
    uint64_t key = (static_cast<uint64_t>(lo) << 32) | static_cast<uint64_t>(hi);

    auto it = interfaceEqAuxVars_.find(key);
    if (it != interfaceEqAuxVars_.end()) return it->second;

    std::string va = getVarNameForSharedTerm(a);
    std::string vb = getVarNameForSharedTerm(b);

    bool aIsConst = false, bIsConst = false;
    mpq_class aVal, bVal;
    if (sharedTermRegistry_ && coreIr_) {
        if (const auto* stA = sharedTermRegistry_->get(a)) {
            const auto& exprA = coreIr_->get(stA->coreExpr);
            if (exprA.isConst()) {
                aIsConst = true;
                if (auto* i = std::get_if<int64_t>(&exprA.payload.value)) aVal = mpq_class(*i);
                else if (auto* s = std::get_if<std::string>(&exprA.payload.value)) aVal = mpqFromString(*s);
            }
        }
        if (const auto* stB = sharedTermRegistry_->get(b)) {
            const auto& exprB = coreIr_->get(stB->coreExpr);
            if (exprB.isConst()) {
                bIsConst = true;
                if (auto* i = std::get_if<int64_t>(&exprB.payload.value)) bVal = mpq_class(*i);
                else if (auto* s = std::get_if<std::string>(&exprB.payload.value)) bVal = mpqFromString(*s);
            }
        }
    }

    int aux = -1;
    if (aIsConst && bIsConst) {
        if (aVal == bVal) return -1;
        return -1;
    } else if (aIsConst) {
        if (vb.empty()) return -1;
        int vB = manager_.getOrCreateVar(gs_, vb);
        std::vector<std::pair<int, mpq_class>> terms;
        terms.push_back({vB, mpq_class(1)});
        aux = gs_.addConstraint(terms, aVal);
    } else if (bIsConst) {
        if (va.empty()) return -1;
        int vA = manager_.getOrCreateVar(gs_, va);
        std::vector<std::pair<int, mpq_class>> terms;
        terms.push_back({vA, mpq_class(1)});
        aux = gs_.addConstraint(terms, bVal);
    } else {
        if (va.empty() || vb.empty()) return -1;
        std::vector<std::pair<int, mpq_class>> terms;
        terms.push_back({manager_.getOrCreateVar(gs_, va), mpq_class(1)});
        terms.push_back({manager_.getOrCreateVar(gs_, vb), mpq_class(-1)});
        aux = gs_.addConstraint(terms, mpq_class(0));
    }

    interfaceEqAuxVars_[key] = aux;
    return aux;
}

std::vector<SatLit>
LiaSolver::assertedVarEqualityReason(SharedTermId a, SharedTermId b) const {
    if (!sharedTermRegistry_) return {};
    // Names of the two (non-const) shared variables.
    auto nameOf = [&](SharedTermId s) -> std::string {
        if (const auto* st = sharedTermRegistry_->get(s)) {
            if (coreIr_ && coreIr_->get(st->coreExpr).isConst()) return "";
            auto it = sharedTermToVarName_.find(s);
            if (it != sharedTermToVarName_.end()) return it->second;
            const auto& e = coreIr_->get(st->coreExpr);
            if (e.kind == Kind::Variable &&
                std::holds_alternative<std::string>(e.payload.value)) {
                return std::get<std::string>(e.payload.value);
            }
        }
        return "";
    };
    std::string na = nameOf(a), nb = nameOf(b);
    if (na.empty() || nb.empty() || na == nb) return {};

    // Aggregate the asserted linear (in)equality atoms whose canonical LHS is a
    // 2-variable difference form {(na,c),(nb,-c)} into a single interval on the
    // normalized difference d = (na - nb). Each atom contributes a lower and/or
    // upper bound on d (after dividing by c and flipping for negative c). If the
    // accumulated interval pins d == 0, then na = nb is entailed and we return
    // the reason literals of the atoms that did the pinning. This covers BOTH
    // an explicit equality atom (na - nb = 0; both bounds 0 — repro R4) and two
    // complementary inequalities (na <= nb and nb <= na ⟹ na = nb — repro e6).
    bool haveLo = false, haveUp = false;
    mpq_class lo = 0, up = 0;
    SatLit loLit{}, upLit{};
    for (const auto& e : theoryTrail_) {
        if (e.isDiseq) continue;
        if (!std::holds_alternative<LinearAtomPayload>(e.atom.payload)) continue;
        const auto& payload = std::get<LinearAtomPayload>(e.atom.payload);
        if (payload.lhs.terms.size() != 2) continue;
        const auto& t0 = payload.lhs.terms[0];
        const auto& t1 = payload.lhs.terms[1];
        if (t0.second == 0 || t0.second != -t1.second) continue;  // form c*x - c*y
        // Orient so that the form reads (na - nb) * c0.
        mpq_class c0;
        if (t0.first == na && t1.first == nb)      c0 = t0.second;   // (na - nb)*c0
        else if (t0.first == nb && t1.first == na) c0 = t1.second;   // (na - nb)*c0
        else continue;
        // payload: (form) rel rhs, asserted with polarity e.value. Effective
        // relation on the form value F = c0*(na-nb):
        Relation rel = e.value ? payload.rel : negateRelation(payload.rel);
        const mpq_class& rhs = payload.rhs.asRational();
        // Reduce to bounds on d = na - nb: F = c0*d, F rel rhs  ⟹  d rel' rhs/c0.
        mpq_class bnd = rhs / c0;
        bool flip = (c0 < 0);
        auto addLower = [&](const mpq_class& v, SatLit lit) {
            if (!haveLo || v > lo) { lo = v; loLit = lit; haveLo = true; }
        };
        auto addUpper = [&](const mpq_class& v, SatLit lit) {
            if (!haveUp || v < up) { up = v; upLit = lit; haveUp = true; }
        };
        switch (rel) {
            case Relation::Eq:
                addLower(bnd, e.lit); addUpper(bnd, e.lit); break;
            case Relation::Leq:
                if (!flip) addUpper(bnd, e.lit); else addLower(bnd, e.lit); break;
            case Relation::Geq:
                if (!flip) addLower(bnd, e.lit); else addUpper(bnd, e.lit); break;
            case Relation::Lt:    // integers: d < bnd  ⟺  d <= bnd-1 (only used to pin via combo; treat conservatively as <= for difference-equality detection only when integral)
            case Relation::Gt:
            default:
                break;  // strict bounds don't pin an equality; skip
        }
    }
    if (haveLo && haveUp && lo == 0 && up == 0) {
        std::vector<SatLit> reasons;
        reasons.push_back(loLit);
        if (!(upLit == loLit)) reasons.push_back(upLit);
        return reasons;
    }
    return {};
}

TheoryCheckResult LiaSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    int aux = getOrCreateInterfaceEqAuxVar(a, b);
    if (aux < 0) return TheoryCheckResult::consistent();

    // Remove stale disequality for the same pair
    auto it = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
        [a, b](const auto& d) { return d.a == a && d.b == b; });
    interfaceDisequalities_.erase(it, interfaceDisequalities_.end());

    interfaceEqualities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

TheoryCheckResult LiaSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    int aux = getOrCreateInterfaceEqAuxVar(a, b);
    if (aux < 0) return TheoryCheckResult::consistent();

    // Remove stale equality for the same pair
    auto it = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
        [a, b](const auto& e) { return e.a == a && e.b == b; });
    interfaceEqualities_.erase(it, interfaceEqualities_.end());

    interfaceDisequalities_.push_back({a, b, reason, level});
    // Invalidate simplex state because an interface disequality may remove a
    // previously-applied interface equality bound.  Force full rebuild on next check.
    gs_.resetActiveBounds();
    appliedCursor_ = 0;
    return TheoryCheckResult::consistent();
}

// Track A mirror for LIA (see LraSolver::tryProvePairEqualityByLpDuality for
// the discipline). Same RAII, marker filter, conflict-state clear.
bool LiaSolver::tryProvePairEqualityByLpDuality(int aux, std::vector<SatLit>& outReasons) {
    static const SatLit MARKER{0, true};
    struct ProbeScope {
        GeneralSimplex& gs;
        int level;
        ProbeScope(GeneralSimplex& g, int lvl) : gs(g), level(lvl) { gs.push(); }
        ~ProbeScope() { gs.pop(); gs.backtrackToLevel(level); }
        ProbeScope(const ProbeScope&) = delete;
        ProbeScope& operator=(const ProbeScope&) = delete;
    };
    auto collectAndFilter = [&](std::vector<SatLit>& out) {
        for (const auto& br : gs_.getConflict()) {
            if (br.reason == MARKER) continue;
            out.push_back(br.reason);
        }
    };
    std::vector<SatLit> upperReasons, lowerReasons;
    {
        ProbeScope scope(gs_, currentLevel_);
        BoundInfo strict(BoundValue(DeltaRational(mpq_class(0), mpq_class(-1))), MARKER);
        bool ok = gs_.assertUpper(aux, strict, currentLevel_);
        bool unsat = !ok || gs_.check() == GeneralSimplex::Result::Unsat;
        if (unsat) collectAndFilter(upperReasons);
        if (!unsat) return false;
    }
    {
        ProbeScope scope(gs_, currentLevel_);
        BoundInfo strict(BoundValue(DeltaRational(mpq_class(0), mpq_class(1))), MARKER);
        bool ok = gs_.assertLower(aux, strict, currentLevel_);
        bool unsat = !ok || gs_.check() == GeneralSimplex::Result::Unsat;
        if (unsat) collectAndFilter(lowerReasons);
        if (!unsat) return false;
    }
    outReasons = std::move(upperReasons);
    outReasons.insert(outReasons.end(), lowerReasons.begin(), lowerReasons.end());
    std::sort(outReasons.begin(), outReasons.end(),
        [](SatLit a, SatLit b) {
            if (a.var != b.var) return a.var < b.var;
            return a.sign < b.sign;
        });
    outReasons.erase(std::unique(outReasons.begin(), outReasons.end(),
        [](SatLit a, SatLit b) {
            return a.var == b.var && a.sign == b.sign;
        }), outReasons.end());
    assert(std::none_of(outReasons.begin(), outReasons.end(),
        [](const SatLit& r) { return r == MARKER; }) &&
        "Track A LIA: marker bound leaked into emitted reason set");
    return true;
}

std::vector<TheorySolver::SharedEqualityPropagation>
LiaSolver::getDeducedSharedEqualities() {
    if (!sharedTermRegistry_) return {};

    // Build name -> simplex var map
    std::unordered_map<std::string, int> nameToVar;
    for (int i = 0; i < gs_.numVars(); ++i) {
        nameToVar[gs_.varName(i)] = i;
    }

    // Map fixed-value shared terms
    using GroupEntry = std::pair<SharedTermId, std::vector<SatLit>>;
    std::map<DeltaRational, std::vector<GroupEntry>> groups;

    for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
        std::string name = getVarNameForSharedTerm(stId);
        if (name.empty()) continue;
        auto it = nameToVar.find(name);
        if (it == nameToVar.end()) continue;
        int var = it->second;

        auto fixedOpt = gs_.proveFixedValue(var);
        if (!fixedOpt) continue;

        const DeltaRational& val = fixedOpt->first;
        std::vector<SatLit> reasons;
        for (const auto& br : fixedOpt->second) {
            reasons.push_back(br.reason);
        }
        std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
            return a.var < b.var || (a.var == b.var && a.sign < b.sign);
        });
        reasons.erase(std::unique(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
            return a.var == b.var && a.sign == b.sign;
        }), reasons.end());
        groups[val].push_back({stId, std::move(reasons)});
    }

    std::vector<TheorySolver::SharedEqualityPropagation> result;
    for (auto& [valKey, terms] : groups) {
        if (terms.size() < 2) continue;
        for (size_t i = 0; i < terms.size(); ++i) {
            for (size_t j = i + 1; j < terms.size(); ++j) {
                std::vector<SatLit> reasons;
                reasons.insert(reasons.end(), terms[i].second.begin(), terms[i].second.end());
                reasons.insert(reasons.end(), terms[j].second.begin(), terms[j].second.end());
                std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
                    return a.var < b.var || (a.var == b.var && a.sign < b.sign);
                });
                reasons.erase(std::unique(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
                    return a.var == b.var && a.sign == b.sign;
                }), reasons.end());
                result.push_back(TheorySolver::SharedEqualityPropagation{terms[i].first, terms[j].first, std::move(reasons)});
            }
        }
    }

    // Variable-variable implied equalities. The fixed-value grouping above only
    // catches terms pinned to a constant. But asserted linear facts can make two
    // shared variables equal WITHOUT fixing either to a value: an equality atom
    // (+ i 1)=(+ j 1) normalizing to (i - j = 0) (repro R4), or two
    // complementary inequalities i<=j and j<=i pinning (i - j) to 0 (repro e6).
    // Such implied equalities must be propagated to EUF so array Row1/congruence
    // fires (select(store(a,i,v),j) with i=j collapses to v). For each pair of
    // NON-constant shared variables, assertedVarEqualityReason reports the
    // proving reason literals (or empty). Sound: only fires when the asserted
    // atoms genuinely pin the difference to 0. Bounded by #distinct shared vars.
    {
        std::vector<SharedTermId> sharedVars;
        for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
            if (const auto* st = sharedTermRegistry_->get(stId)) {
                if (coreIr_ && coreIr_->get(st->coreExpr).isConst()) continue;
            }
            std::string nm = getVarNameForSharedTerm(stId);
            if (nm.empty()) continue;
            if (nameToVar.find(nm) == nameToVar.end()) continue;
            sharedVars.push_back(stId);
        }
        const int n = static_cast<int>(sharedVars.size());
        std::vector<std::vector<std::pair<int, std::vector<SatLit>>>> adj(n);
        for (int i = 0; i < n; ++i) {
            for (int j = i + 1; j < n; ++j) {
                auto reasons = assertedVarEqualityReason(sharedVars[i], sharedVars[j]);
                if (reasons.empty()) continue;
                adj[i].push_back({j, reasons});
                adj[j].push_back({i, reasons});
                result.push_back(TheorySolver::SharedEqualityPropagation{
                    sharedVars[i], sharedVars[j], std::move(reasons)});
            }
        }

        // Track 2b Step 1 (XOLVER_SIMPLEX_IMPLIED_EQ): transitive closure over
        // the direct-pair edges. If two shared vars are linked through a chain
        // of asserted equalities (x = z and z = y), emit x = y too with the
        // UNION of all SatLits along the BFS path. Sound by construction.
        // Deduped against direct pairs emitted above.
        if (impliedEqEnabled_ && n > 2) {
            auto pairKey = [](int a, int b) -> uint64_t {
                int lo = std::min(a, b), hi = std::max(a, b);
                return (static_cast<uint64_t>(lo) << 32) | static_cast<uint32_t>(hi);
            };
            std::unordered_set<uint64_t> emittedPair;
            for (int i = 0; i < n; ++i)
                for (const auto& [j, rs] : adj[i])
                    if (i < j) emittedPair.insert(pairKey(i, j));
            for (int i = 0; i < n; ++i) {
                std::vector<int> parent(n, -1);
                std::vector<std::vector<SatLit>> edgeRs(n);
                std::vector<int> bfs;
                parent[i] = i;
                bfs.push_back(i);
                for (size_t head = 0; head < bfs.size(); ++head) {
                    int u = bfs[head];
                    for (const auto& [v, rs] : adj[u]) {
                        if (parent[v] != -1) continue;
                        parent[v] = u;
                        edgeRs[v] = rs;
                        bfs.push_back(v);
                    }
                }
                for (int j = i + 1; j < n; ++j) {
                    if (parent[j] == -1) continue;
                    if (emittedPair.count(pairKey(i, j))) continue;
                    std::vector<SatLit> chain;
                    for (int cur = j; cur != i; cur = parent[cur])
                        for (SatLit s : edgeRs[cur]) chain.push_back(s);
                    std::sort(chain.begin(), chain.end(),
                        [](SatLit a, SatLit b) {
                            if (a.var != b.var) return a.var < b.var;
                            return a.sign < b.sign;
                        });
                    chain.erase(std::unique(chain.begin(), chain.end(),
                        [](SatLit a, SatLit b) {
                            return a.var == b.var && a.sign == b.sign;
                        }), chain.end());
                    emittedPair.insert(pairKey(i, j));
                    result.push_back(TheorySolver::SharedEqualityPropagation{
                        sharedVars[i], sharedVars[j], std::move(chain)});
                }
            }
        }
    }

    // Definitional-form implied equalities (N-variable). assertedVarEqualityReason
    // only pins a 2-variable DIFFERENCE atom (na - nb = 0). But two shared vars
    // each asserted equal to the SAME linear form via SEPARATE multi-variable
    // equalities (e.g. `bridge = bz+ba` and `q = bz+ba`, two 3-var equalities)
    // are equal by transitivity through the shared form — a linear COMBINATION the
    // 2-var scan cannot see. This is the computed-array-index combination case
    // (read2): the LIA-entailed index equality must reach EUF so array Row1/Row2
    // fires. For each active equality atom and each shared var v in it, build the
    // canonical isolated form  v = rhs/c_v - sum_{u!=v} (c_u/c_v) u ; shared vars
    // with IDENTICAL canonical forms are entailed equal. Reason = the two defining
    // atoms only (the other vars cancel, so they need not appear). SOUND: v1=F and
    // v2=F entail v1=v2 from exactly those two atoms; an entailed equality only
    // aids N-O completeness, never a wrong verdict.
    {
        std::unordered_map<std::string, SharedTermId> nameToShared;
        for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
            if (const auto* st = sharedTermRegistry_->get(stId)) {
                if (coreIr_ && coreIr_->get(st->coreExpr).isConst()) continue;  // consts handled by fixed-value grouping
            }
            std::string nm = getVarNameForSharedTerm(stId);
            if (!nm.empty()) nameToShared.emplace(nm, stId);
        }
        // canonical isolated-form key -> [(sharedVar, defining-atom literal)]
        std::map<std::string, std::vector<std::pair<SharedTermId, SatLit>>> byForm;
        for (const auto& e : theoryTrail_) {
            if (e.isDiseq || !e.value) continue;
            if (!std::holds_alternative<LinearAtomPayload>(e.atom.payload)) continue;
            const auto& p = std::get<LinearAtomPayload>(e.atom.payload);
            if (p.rel != Relation::Eq) continue;
            const auto& terms = p.lhs.terms;  // sorted by var name
            if (terms.size() < 2) continue;   // 2-var handled above; need >=2 here too
            const mpq_class& rhs = p.rhs.asRational();
            for (size_t vi = 0; vi < terms.size(); ++vi) {
                auto sit = nameToShared.find(terms[vi].first);
                if (sit == nameToShared.end()) continue;   // v not shared
                const mpq_class& cv = terms[vi].second;
                if (cv == 0) continue;
                // Canonical key: const rhs/cv, then (u, -c_u/cv) for u != v
                // (terms stay name-sorted with vi removed).
                std::string key = mpq_class(rhs / cv).get_str();
                key.push_back('|');
                for (size_t ui = 0; ui < terms.size(); ++ui) {
                    if (ui == vi) continue;
                    key += terms[ui].first;
                    key.push_back(':');
                    key += mpq_class(-terms[ui].second / cv).get_str();
                    key.push_back(';');
                }
                byForm[key].push_back({sit->second, e.lit});
            }
        }
        // REPRESENTATIVE-based emission (NOT pairwise): publish only v = rep for
        // each non-rep bucket member, O(g) instead of O(g^2). EUF /
        // SharedEqualityManager transitive closure derives the remaining
        // member-member equalities (v1=rep, v2=rep => v1=v2). Each v=rep stays
        // soundly explained by the two defining atoms. This is an interim N-O
        // completeness step; the production design is demand-driven (Array posts
        // a (storeIndex,readIndex) ProveEq demand, this oracle answers only that
        // pair) — see [[project_array_reasoning]].
        for (auto& [key, group] : byForm) {
            (void)key;
            if (group.size() < 2) continue;
            const auto& rep = group.front();
            for (size_t k = 1; k < group.size(); ++k) {
                if (group[k].first == rep.first) continue;  // same shared term
                result.push_back(TheorySolver::SharedEqualityPropagation{
                    group[k].first, rep.first,
                    std::vector<SatLit>{group[k].second, rep.second}});
            }
        }
    }

    return result;
}

std::vector<TheorySolver::SharedEqualityPropagation>
LiaSolver::deduceIndexEqualitiesByGaussian(const std::vector<SharedTermId>& idxTerms) {
    std::vector<TheorySolver::SharedEqualityPropagation> result;
    if (!sharedTermRegistry_ || idxTerms.size() < 2) return result;

    // Map each shared array-index term to its simplex var NAME (skip constants).
    std::vector<std::pair<SharedTermId, std::string>> idxVars;
    for (SharedTermId s : idxTerms) {
        if (const auto* st = sharedTermRegistry_->get(s)) {
            if (coreIr_ && coreIr_->get(st->coreExpr).isConst()) continue;
        }
        std::string nm = getVarNameForSharedTerm(s);
        if (!nm.empty()) idxVars.push_back({s, nm});
    }
    if (idxVars.size() < 2) return result;

    // Coordinate space: 0 = ONE (constant), 1.. = variables by name. Each asserted
    // equality `sum c_v v = r` becomes the homogeneous form `sum c_v v - r*ONE = 0`.
    std::unordered_map<std::string, int> varCoord;
    auto coordOf = [&](const std::string& nm) -> int {
        auto it = varCoord.find(nm);
        if (it != varCoord.end()) return it->second;
        int c = static_cast<int>(varCoord.size()) + 1;  // 0 reserved for ONE
        varCoord[nm] = c;
        return c;
    };

    struct Row { std::map<int, mpq_class> coeffs; std::vector<SatLit> reason; };
    std::vector<Row> rows;
    for (const auto& e : theoryTrail_) {
        if (e.isDiseq || !e.value) continue;
        if (!std::holds_alternative<LinearAtomPayload>(e.atom.payload)) continue;
        const auto& p = std::get<LinearAtomPayload>(e.atom.payload);
        if (p.rel != Relation::Eq) continue;
        Row r;
        for (const auto& t : p.lhs.terms)
            if (t.second != 0) r.coeffs[coordOf(t.first)] += t.second;
        const mpq_class& rhs = p.rhs.asRational();
        if (rhs != 0) r.coeffs[0] += -rhs;   // ONE coord
        for (auto it = r.coeffs.begin(); it != r.coeffs.end(); )
            (it->second == 0) ? it = r.coeffs.erase(it) : ++it;
        if (r.coeffs.empty()) continue;
        r.reason.push_back(e.lit);
        rows.push_back(std::move(r));
    }
    if (rows.empty()) return result;

    // Forward-eliminate to row echelon, keyed by leading (smallest) coord; each
    // pivot is normalized to lead-coeff 1 and carries the reasons of the atoms
    // combined into it. reduce() subtracts pivots from a row, accumulating reasons.
    std::map<int, Row> pivotByLead;
    auto reduce = [&](Row& r) {
        for (;;) {
            int hit = -1;
            for (const auto& kv : r.coeffs)
                if (pivotByLead.count(kv.first)) { hit = kv.first; break; }
            if (hit < 0) break;
            const Row& piv = pivotByLead[hit];
            mpq_class factor = r.coeffs[hit];   // piv lead coeff == 1
            for (const auto& [pc, pv] : piv.coeffs) {
                mpq_class nv = r.coeffs[pc] - factor * pv;
                if (nv == 0) r.coeffs.erase(pc); else r.coeffs[pc] = nv;
            }
            r.reason.insert(r.reason.end(), piv.reason.begin(), piv.reason.end());
        }
    };
    for (auto& row : rows) {
        reduce(row);
        if (row.coeffs.empty()) continue;  // redundant (already spanned)
        int lc = row.coeffs.begin()->first;
        mpq_class lcoeff = row.coeffs[lc];
        if (lcoeff != 1) for (auto& [c, v] : row.coeffs) v /= lcoeff;
        pivotByLead[lc] = std::move(row);
    }

    auto dedupReasons = [](std::vector<SatLit>& rs) {
        std::sort(rs.begin(), rs.end(), [](SatLit a, SatLit b) {
            return a.var < b.var || (a.var == b.var && a.sign < b.sign);
        });
        rs.erase(std::unique(rs.begin(), rs.end(), [](SatLit a, SatLit b) {
            return a.var == b.var && a.sign == b.sign;
        }), rs.end());
    };

    // For each array-index pair, test whether (a - b) reduces to the zero form:
    // if so, a = b is entailed by the combining atoms (the accumulated reasons).
    for (size_t i = 0; i < idxVars.size(); ++i) {
        for (size_t j = i + 1; j < idxVars.size(); ++j) {
            if (idxVars[i].second == idxVars[j].second) continue;
            Row target;
            target.coeffs[coordOf(idxVars[i].second)] += 1;
            target.coeffs[coordOf(idxVars[j].second)] += -1;
            for (auto it = target.coeffs.begin(); it != target.coeffs.end(); )
                (it->second == 0) ? it = target.coeffs.erase(it) : ++it;
            reduce(target);
            if (!target.coeffs.empty()) continue;  // a-b not entailed 0
            dedupReasons(target.reason);
            if (target.reason.empty()) continue;   // defensive: need a reason
            result.push_back(TheorySolver::SharedEqualityPropagation{
                idxVars[i].first, idxVars[j].first, std::move(target.reason)});
        }
    }
    return result;
}

std::vector<SatLit> LiaSolver::allActiveReasons() const {
    std::vector<SatLit> rs;
    rs.reserve(theoryTrail_.size() + interfaceEqualities_.size() + interfaceDisequalities_.size());
    for (const auto& e : theoryTrail_) {
        rs.push_back(e.lit);
    }
    for (const auto& ieq : interfaceEqualities_) {
        rs.push_back(ieq.reason);
    }
    for (const auto& idiseq : interfaceDisequalities_) {
        rs.push_back(idiseq.reason);
    }
    std::sort(rs.begin(), rs.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    rs.erase(std::unique(rs.begin(), rs.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), rs.end());
    return rs;
}

void LiaSolver::allowInterfaceDiseqModelBranch(SharedTermId a, SharedTermId b) {
    SharedTermId lo = a < b ? a : b;
    SharedTermId hi = a < b ? b : a;
    uint64_t key = (static_cast<uint64_t>(lo) << 32) | static_cast<uint64_t>(hi);
    diseqBranchAuthorized_.insert(key);
}

std::optional<RealValue> LiaSolver::sharedTermArithValue(SharedTermId s) const {
    if (!sharedTermRegistry_ || !coreIr_) return std::nullopt;
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return std::nullopt;
    const auto& expr = coreIr_->get(st->coreExpr);
    if (expr.kind == Kind::ConstInt) {
        if (auto* iv = std::get_if<int64_t>(&expr.payload.value))
            return RealValue::fromMpq(mpq_class(*iv));
        if (auto* sv = std::get_if<std::string>(&expr.payload.value))
            return RealValue::fromMpq(mpqFromString(*sv));  // large literal (string payload)
    }
    if (expr.kind == Kind::ConstReal) {
        if (auto* sv = std::get_if<std::string>(&expr.payload.value))
            return RealValue::fromMpq(mpqFromString(*sv));
    }
    if (expr.kind != Kind::Variable ||
        !std::holds_alternative<std::string>(expr.payload.value)) {
        return std::nullopt;
    }
    const std::string& name = std::get<std::string>(expr.payload.value);
    // Keep shared-term values consistent with a repaired integer model if one
    // was produced (defensive — repair is gated off when interface constraints
    // are active, so this normally never differs from gs_).
    if (repairModel_) {
        auto it = repairModel_->find(name);
        if (it != repairModel_->end()) return RealValue::fromMpq(it->second);
    }
    int idx = manager_.findVarIndex(name);
    if (idx < 0) return std::nullopt;
    DeltaRational val = gs_.value(idx);
    // Integer model values are integral after check(); the delta part is an
    // infinitesimal that does not affect the integer comparison.
    return RealValue::fromMpq(val.a);
}

std::optional<TheorySolver::TheoryModel> LiaSolver::getModel() const {
    // If a rounding repair produced the SAT verdict, the simplex β holds the
    // fractional relaxation, not the integer model — return the repaired point.
    if (repairModel_) {
        TheoryModel model;
        for (const auto& [name, val] : *repairModel_) {
            if (name.empty()) continue;
            if (name.size() >= 2 && name[0] == '_' && name[1] == '_') continue;
            model.assignments[name] = val.get_num().get_str();
            model.numericAssignments.insert({name, RealValue::fromMpq(val)});
        }
        if (model.assignments.empty()) return std::nullopt;
        return model;
    }
    TheoryModel model;
    for (int i = 0; i < gs_.numVars(); ++i) {
        std::string name = manager_.getVarName(i);
        if (name.empty()) continue;           // skip auxiliary vars
        if (name.size() >= 2 && name[0] == '_' && name[1] == '_') continue; // internal
        DeltaRational val = gs_.value(i);
        // For integer variables, value should be integral after check().
        // If delta component is non-zero, take the rational part (delta is infinitesimal).
        if (val.b == 0 && val.a.get_den() == 1) {
            model.assignments[name] = val.a.get_num().get_str();
        } else {
            model.assignments[name] = val.a.get_str();
        }
        model.numericAssignments.insert({name, RealValue::fromMpq(val.a)});
    }
    if (model.assignments.empty()) return std::nullopt;
    return model;
}

// ============================================================================
// Debug dump helpers
// ============================================================================

std::string LiaSolver::mpqToSmtLib(const mpq_class& q) {
    if (q.get_den() == 1) {
        return q.get_num().get_str();
    }
    return "(/ " + q.get_num().get_str() + " " + q.get_den().get_str() + ")";
}

std::string LiaSolver::relationToSmtLib(Relation rel) {
    switch (rel) {
        case Relation::Eq:  return "=";
        case Relation::Lt:  return "<";
        case Relation::Leq: return "<=";
        case Relation::Gt:  return ">";
        case Relation::Geq: return ">=";
        case Relation::Neq: return "distinct";
    }
    return "=";
}

std::string LiaSolver::linearFormToSmtLib(const LinearFormKey& form) {
    if (form.terms.empty()) return "0";
    if (form.terms.size() == 1) {
        const auto& [name, coeff] = form.terms[0];
        if (coeff == 1) return name;
        if (coeff == -1) return "(- " + name + ")";
        return "(* " + mpqToSmtLib(coeff) + " " + name + ")";
    }
    std::string s = "(+";
    for (const auto& [name, coeff] : form.terms) {
        if (coeff == 1) {
            s += " " + name;
        } else if (coeff == -1) {
            s += " (- " + name + ")";
        } else {
            s += " (* " + mpqToSmtLib(coeff) + " " + name + ")";
        }
    }
    s += ")";
    return s;
}

void LiaSolver::dumpState(const std::string& tag) const {
    const char* env = std::getenv("XOLVER_LIA_DUMP_DIR");
    if (!env || !*env) return;
    std::filesystem::path dir(env);
    if (!std::filesystem::exists(dir)) {
        std::filesystem::create_directories(dir);
    }

    int id = ++dumpCounter_;
    std::filesystem::path path = dir / ("lia_dump_" + std::to_string(id) + "_" + tag + ".smt2");
    std::ofstream ofs(path);
    if (!ofs) return;

    ofs << "(set-logic QF_LIA)\n";

    // Collect all variable names
    std::unordered_set<std::string> vars;
    for (const auto& a : activeAtoms_) {
        for (const auto& t : a.lhs.terms) vars.insert(t.first);
    }
    for (const auto& d : disequalities_) {
        for (const auto& t : d.lhs.terms) vars.insert(t.first);
    }
    for (const auto& ie : interfaceEqualities_) {
        (void)ie;
    }

    for (const auto& v : vars) {
        ofs << "(declare-fun " << v << " () Int)\n";
    }

    // Active atoms
    for (const auto& a : activeAtoms_) {
        Relation effectiveRel = a.value ? a.rel : negateRelation(a.rel);
        std::string lhsStr = linearFormToSmtLib(a.lhs);
        std::string rhsStr = mpqToSmtLib(a.rhs);
        if (effectiveRel == Relation::Neq) {
            ofs << "(assert (distinct " << lhsStr << " " << rhsStr << "))\n";
        } else {
            ofs << "(assert (" << relationToSmtLib(effectiveRel) << " " << lhsStr << " " << rhsStr << "))\n";
        }
    }

    // Disequalities
    for (const auto& d : disequalities_) {
        std::string lhsStr = linearFormToSmtLib(d.lhs);
        std::string rhsStr = mpqToSmtLib(d.rhs);
        ofs << "(assert (distinct " << lhsStr << " " << rhsStr << "))\n";
    }

    ofs << "(check-sat)\n";

    if (tag == "sat") {
        ofs << "(get-model)\n";
    }

    ofs.flush();
}

} // namespace xolver
