#include "util/MpqUtils.h"
#include "theory/arith/lra/LraSolver.h"
#include "util/MpqUtils.h"
#include "util/EnvParam.h"
#include "theory/arith/Reasoner.h"
#include "theory/core/DebugTrace.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/arith/linear/SimplexDiseqSplitter.h"
#include "theory/core/TheoryAtomTypes.h"
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <iostream>

namespace xolver {

LraSolver::LraSolver() {
    // Phase 2: single core reasoner (incremental replay + interface eqs +
    // simplex + disequality split + propagation).
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "lra.core",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCore(db, e); }));

    // XOLVER_LRA_PROP (default OFF): lift sound Farkas row-propagations to the
    // SAT solver during search. Read once.
    const char* prop = std::getenv("XOLVER_LRA_PROP");
    lraPropEnabled_ = (prop && *prop && *prop != '0');
    // XOLVER_SIMPLEX_IMPLIED_EQ (default OFF): see header comment.
    const char* impl = std::getenv("XOLVER_SIMPLEX_IMPLIED_EQ");
    impliedEqEnabled_ = (impl && *impl && *impl != '0');
    lpDualityBudget_ = std::max(
        0, env::paramInt("XOLVER_LRA_LP_DUALITY_BUDGET", lpDualityBudget_));
}

LraSolver::~LraSolver() {
#ifdef XOLVER_LRA_PROFILE
    if (profile_.checkCalls > 0) {
        profile_.dump();
    }
#endif
}

void LraSolver::onPush() {
    gs_.push();
}

void LraSolver::onPop(uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) {
        gs_.pop();
    }
}

void LraSolver::onReset() {
#ifdef XOLVER_LRA_PROFILE
    if (profile_.checkCalls > 0) {
        profile_.dump();
    }
    profile_.resetForNewSolve();
#endif
    theoryTrail_.clear();
    appliedCursor_ = 0;
    pendingConflict_.reset();
    diseqBranchAuthorized_.clear();
    atomEvalCache_.clear();
    gs_.resetActiveBounds();
}

void LraSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) {
    if (!std::holds_alternative<LinearAtomPayload>(atom.payload)) return;

    const auto& payload = std::get<LinearAtomPayload>(atom.payload);
    // LRA bounds are rational; an algebraic RHS never arises from inputs.
    const mpq_class& rhs = payload.rhs.asRational();
    int auxVar = manager_.getOrCreateAuxVar(gs_, payload.lhs, rhs);
    auxFormInfo_[auxVar] = {payload.lhs, rhs};
    Relation effectiveRel = value ? payload.rel : negateRelation(payload.rel);
    bool isDiseq = (effectiveRel == Relation::Neq);

    for (auto& e : theoryTrail_) {
        if (e.atom.satVar == atom.satVar) {
            if (e.isDiseq) {
                // Remove stale disequality from incremental cache.
                auto it = std::remove_if(activeDisequalities_.begin(), activeDisequalities_.end(),
                    [&e](const auto& d) { return d.lit == e.lit; });
                activeDisequalities_.erase(it, activeDisequalities_.end());
            }
            e = {level, assertedLit, atom, value, auxVar, isDiseq};
            if (isDiseq) {
                activeDisequalities_.push_back({auxVar, payload.lhs, rhs, assertedLit, level});
            }
            return;
        }
    }
    theoryTrail_.push_back({level, assertedLit, atom, value, auxVar, isDiseq});

    if (isDiseq) {
        activeDisequalities_.push_back({auxVar, payload.lhs, rhs, assertedLit, level});
    }
}

void LraSolver::onBacktrack(int level) {
    currentLevel_ = level;

    if (level == 0) {
        // Full reset for modelCheck rebuild or SAT restart to level 0.
        gs_.resetActiveBounds();
        theoryTrail_.clear();
        activeDisequalities_.clear();
        interfaceEqualities_.clear();
        interfaceDisequalities_.clear();
    } else {
        // Backtrack GeneralSimplex bounds by SAT decision level.
        gs_.backtrackToLevel(level);

        // Synchronize theory trail.
        while (!theoryTrail_.empty() && theoryTrail_.back().level > level) {
            theoryTrail_.pop_back();
        }

        // Interface equalities / disequalities
        auto ieIt = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
            [level](const auto& ie) { return ie.level > level; });
        interfaceEqualities_.erase(ieIt, interfaceEqualities_.end());

        auto idIt = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
            [level](const auto& ie) { return ie.level > level; });
        interfaceDisequalities_.erase(idIt, interfaceDisequalities_.end());

        // Phase 2: sync active disequalities cache
        auto adIt = std::remove_if(activeDisequalities_.begin(), activeDisequalities_.end(),
            [level](const auto& d) { return d.level > level; });
        activeDisequalities_.erase(adIt, activeDisequalities_.end());
    }
    if (appliedCursor_ > theoryTrail_.size()) {
        appliedCursor_ = theoryTrail_.size();
    }

    pendingConflict_.reset();
}

bool LraSolver::applyEntryToSimplex(const LraTrailEntry& e) {
    const auto& payload = std::get<LinearAtomPayload>(e.atom.payload);
    Relation effectiveRel = e.value ? payload.rel : negateRelation(payload.rel);

    if (effectiveRel == Relation::Neq) {
        // Disequalities are handled after simplex check, not as bounds.
        return true;
    }

    return manager_.assertBound(gs_, e.auxVar, payload.rel, e.value, e.lit, e.level);
}

std::optional<TheoryCheckResult> LraSolver::stageCore(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    NO_DBG << "[LRA] check begin\n";
    entailmentProps_.clear();  // buffer holds only this check's propagations

#ifdef XOLVER_LRA_PROFILE
    profile_.checkCalls++;
    int currentActive = static_cast<int>(theoryTrail_.size() + interfaceEqualities_.size() + interfaceDisequalities_.size());
    profile_.totalActiveLiterals += currentActive;
    if (currentActive > profile_.maxActiveLiterals) profile_.maxActiveLiterals = currentActive;
    profile_.totalNewLiterals += std::max(0, currentActive - profile_.prevActiveCount);
    profile_.prevActiveCount = currentActive;
    auto prof_t0 = std::chrono::steady_clock::now();
#endif

    if (pendingConflict_) {
        return *pendingConflict_;
    }

    // -------------------------------------------------------------------------
    // Phase 1: incremental replay of new trail entries
    // -------------------------------------------------------------------------
    NO_DBG << "[LRA] theoryTrail=" << theoryTrail_.size()
           << " appliedCursor=" << appliedCursor_ << "\n";

    while (appliedCursor_ < theoryTrail_.size()) {
        const auto& e = theoryTrail_[appliedCursor_];
        NO_DBG << "[LRA] replay lit=" << debug::fmtLit(e.lit)
               << " level=" << e.level << "\n";

        bool ok = applyEntryToSimplex(e);
        ++appliedCursor_;
        if (!ok) {
            auto tc = manager_.translateConflict(gs_);
            NO_DBG << "[LRA] immediate conflict: " << debug::fmtClause(tc.clause) << "\n";
#ifdef XOLVER_LRA_PROFILE
            int sz = static_cast<int>(tc.clause.size());
            profile_.totalConflictSize += sz;
            if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
            profile_.immediateConflictCount++;
#endif
            pendingConflict_ = TheoryCheckResult::mkConflict(std::move(tc));
            return *pendingConflict_;
        }
    }

#ifdef XOLVER_LRA_PROFILE
    auto prof_t1 = std::chrono::steady_clock::now();
    profile_.assertBoundTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t1 - prof_t0).count();
    auto prof_t2 = prof_t1;
#endif

    // -------------------------------------------------------------------------
    // Interface equalities (still full replay for simplicity; usually few)
    // -------------------------------------------------------------------------
    NO_DBG << "[LRA] interfaceEqualities=" << interfaceEqualities_.size() << "\n";
    for (const auto& ieq : interfaceEqualities_) {
        int aux = getOrCreateInterfaceEqAuxVar(ieq.a, ieq.b);
        NO_DBG << "[LRA] IEQ st" << ieq.a << " = st" << ieq.b
               << " aux=" << aux
               << " reason=" << debug::fmtLit(ieq.reason)
               << " level=" << ieq.level << "\n";
        if (aux >= 0) {
            bool ok = true;
            ok = gs_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0)), ieq.reason), ieq.level) && ok;
            ok = gs_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0)), ieq.reason), ieq.level) && ok;
            if (!ok) {
                auto tc = manager_.translateConflict(gs_);
                tc.clause.push_back(ieq.reason);
                NO_DBG << "[LRA] IEQ immediate conflict reasons: " << debug::fmtClause(tc.clause) << "\n";
#ifdef XOLVER_LRA_PROFILE
                int sz = static_cast<int>(tc.clause.size());
                profile_.totalConflictSize += sz;
                if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
                profile_.immediateConflictCount++;
#endif
                pendingConflict_ = TheoryCheckResult::mkConflict(std::move(tc));
                return *pendingConflict_;
            }
        }
    }

    auto r = gs_.check();

#ifdef XOLVER_LRA_PROFILE
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
#endif

    NO_DBG << "[LRA] simplex result=" << (r == GeneralSimplex::Result::Sat ? "Sat" :
                                          r == GeneralSimplex::Result::Unsat ? "Unsat" : "Unknown") << "\n";
    if (r == GeneralSimplex::Result::Unsat) {
        auto tc = TheoryConflict{};
        const auto& conflict = gs_.getConflict();
        if (!conflict.empty()) {
            for (const auto& cr : conflict) {
                tc.clause.push_back(cr.reason);
            }
            bool ok = normalizeTheoryClause(tc.clause);
            assert(ok && "complementary literal in theory conflict clause");
            (void)ok;
            NO_DBG << "[LRA] simplex conflict: " << tc.clause.size() << " lits\n";
#ifdef XOLVER_LRA_PROFILE
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
            NO_DBG << "[LRA] fallback conflict (allActiveReasons): " << tc.clause.size() << " lits\n";
#ifdef XOLVER_LRA_PROFILE
            int sz = static_cast<int>(tc.clause.size());
            profile_.totalConflictSize += sz;
            if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
            profile_.fallbackConflictCount++;
#endif
        }
        return TheoryCheckResult::mkConflict(std::move(tc));
    }
    if (r == GeneralSimplex::Result::Unknown) {
        return TheoryCheckResult::unknown();
    }

    // -------------------------------------------------------------------------
    // Phase C: bound propagation (XOLVER_LRA_PROP only). Lift SOUND Farkas
    // bound-propagations to the SAT solver as reason-carrying entailment clauses
    // (¬reasons ∨ implied), verified unit/falsified at the propagator. The old
    // tryConvertDerivedBound path — bare unit lemmas into a dedup-only lemmaDb
    // that was never drained to SAT, AND an over-tight b<0-lower/b>0-upper δ
    // reconstruction — was dead code with a latent unsoundness; removed. When
    // PROP is off we skip propagateAll entirely (it was pure waste before).
    // -------------------------------------------------------------------------
    if (lraPropEnabled_) {
        auto derived = propagationEngine_.propagateAll(gs_);
        const int kMaxProps = 64;
        for (const auto& eb : derived) {
            if (static_cast<int>(entailmentProps_.size()) >= kMaxProps) break;
            if (auto lem = buildEntailmentLemma(eb)) {
                entailmentProps_.push_back(std::move(*lem));
            }
        }
    }

    // Interface disequality vs. an entailed equality: if an asserted 2-var
    // equality atom or two complementary inequalities pin (x - y) to 0, then
    // x = y is entailed and an interface disequality x != y is a hard conflict
    // (proof-carrying: pinning reasons + diseq reason). Catches the
    // QF_ALRA/AUFLRA analogs of R4/e6. Other interface disequalities are left
    // to the convex LRA model (Stage A).
    for (const auto& ieq : interfaceDisequalities_) {
        auto eqReasons = assertedVarEqualityReason(ieq.a, ieq.b);
        // Track B fix: when the narrow 2-var detector misses, also try the
        // LP-duality probe (same detector Track A uses for deduced-eq emission).
        // Without this, SAT can escape Track A's emit by deciding the deduced
        // eq atom FALSE (interface diseq x != y) — LRA would silently accept
        // that diseq even though the polyhedron entails x = y. Closing this
        // path makes BOTH v10002=T (EUF congruence conflict) AND v10002=F
        // (LRA polyhedron conflict) unsat → SAT terminates correctly.
        if (eqReasons.empty() && impliedEqEnabled_) {
            int aux = getOrCreateInterfaceEqAuxVar(ieq.a, ieq.b);
            if (aux >= 0) {
                std::vector<SatLit> probeReasons;
                if (tryProvePairEqualityByLpDuality(aux, probeReasons)) {
                    eqReasons = std::move(probeReasons);
                }
            }
        }
        if (eqReasons.empty()) continue;
        TheoryConflict tc;
        for (auto l : eqReasons) tc.clause.push_back(l);
        tc.clause.push_back(ieq.reason);
        if (normalizeTheoryClause(tc.clause)) {
            return TheoryCheckResult::mkConflict(std::move(tc));
        }
    }

    // -------------------------------------------------------------------------
    // Disequalities: use incremental cache (subset of active trail entries)
    // -------------------------------------------------------------------------
    std::vector<DiseqInfo> disequalities = activeDisequalities_;

    if (!disequalities.empty()) {
#ifdef XOLVER_LRA_PROFILE
        profile_.disequalitySplitCount++;
#endif
        auto dr = handleSimplexDisequalities(
            disequalities, gs_, lemmaDb,
            [this](const DiseqInfo& d) -> TheoryCheckResult {
                if (!registry_) return TheoryCheckResult::consistent();
                auto litLt = registry_->getOrCreateLinearBoundAtom(
                    d.lhs, Relation::Lt, d.rhs, TheoryId::LRA);
                auto litGt = registry_->getOrCreateLinearBoundAtom(
                    d.lhs, Relation::Gt, d.rhs, TheoryId::LRA);
                return TheoryCheckResult::mkLemma(
                    TheoryLemma{{d.lit.negated(), litLt, litGt}});
            });
        if (dr.kind != TheoryCheckResult::Kind::Consistent) return dr;
    }

    // Honor a DECIDED interface disequality the convex model violates. When the
    // SAT solver has committed (a != b) but the simplex point happens to set
    // a = b (both unconstrained -> both pinned to a default), the per-theory
    // model is globally inconsistent. Branch the model apart:
    //   (a != b) => (a - b < 0) OR (a - b > 0).
    // Only at Full effort (a real model is in hand), only when both shared
    // terms resolve to simplex variables (the constant cases are already
    // handled by getOrCreateInterfaceEqAuxVar's const-vs-const refutation), and
    // only after the regular disequality split has nothing left to do — so this
    // is a genuine last-resort separation, not a perturbation of an otherwise
    // resolvable search state.
    if (effort == TheoryEffort::Full && registry_ && !diseqBranchAuthorized_.empty()) {
        for (const auto& ieq : interfaceDisequalities_) {
            // Only model-branch pairs the arrangement split authorized.
            SharedTermId lo = ieq.a < ieq.b ? ieq.a : ieq.b;
            SharedTermId hi = ieq.a < ieq.b ? ieq.b : ieq.a;
            uint64_t key = (static_cast<uint64_t>(lo) << 32) |
                           static_cast<uint64_t>(hi);
            if (!diseqBranchAuthorized_.count(key)) continue;
            std::string va = getVarNameForSharedTerm(ieq.a);
            std::string vb = getVarNameForSharedTerm(ieq.b);
            if (va.empty() || vb.empty() || va == vb) continue;
            int aux = getOrCreateInterfaceEqAuxVar(ieq.a, ieq.b);
            if (aux < 0) continue;
            DeltaRational d = gs_.value(aux);
            if (!(d.a == 0 && d.b == 0)) continue;  // model already separates them
            NO_DBG << "[LRA-DISEQ-BRANCH] " << va << " != " << vb
                   << " but model equates them; branching\n";
            LinearFormKey form;
            form.terms.push_back({va, mpq_class(1)});
            form.terms.push_back({vb, mpq_class(-1)});
            SatLit litLt = registry_->getOrCreateLinearBoundAtom(
                form, Relation::Lt, mpq_class(0), TheoryId::LRA);
            SatLit litGt = registry_->getOrCreateLinearBoundAtom(
                form, Relation::Gt, mpq_class(0), TheoryId::LRA);
            TheoryLemma lemma{{ieq.reason.negated(), litLt, litGt}};
            if (!lemmaDb.contains(lemma)) {
                return TheoryCheckResult::mkLemma(std::move(lemma));
            }
        }
    }

    NO_DBG << "[LRA] Consistent\n";
    return TheoryCheckResult::consistent();
}

// ---------------------------------------------------------------------------
// Nelson-Oppen combination hooks (skeleton for Stage A)
// ---------------------------------------------------------------------------

static std::optional<mpq_class> getConstantRationalValue(const CoreIr& ir, const SharedTermRegistry& reg, SharedTermId s) {
    const auto* st = reg.get(s);
    if (!st) return std::nullopt;
    const auto& expr = ir.get(st->coreExpr);
    if (expr.kind == Kind::ConstInt) {
        if (auto* i = std::get_if<int64_t>(&expr.payload.value)) {
            return mpq_class(*i);
        }
        if (auto* str = std::get_if<std::string>(&expr.payload.value)) {
            return mpqFromString(*str);  // large integer literal (string payload)
        }
    }
    if (expr.kind == Kind::ConstReal) {
        if (auto* str = std::get_if<std::string>(&expr.payload.value)) {
            return mpqFromString(*str);
        }
    }
    return std::nullopt;
}

std::string LraSolver::getVarNameForSharedTerm(SharedTermId s) {
    auto it = sharedTermToVarName_.find(s);
    if (it != sharedTermToVarName_.end()) return it->second;

    if (!sharedTermRegistry_ || !coreIr_) return "";
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return "";

    const auto& expr = coreIr_->get(st->coreExpr);
    if (expr.kind == Kind::Variable) {
        if (std::holds_alternative<std::string>(expr.payload.value)) {
            std::string name = std::get<std::string>(expr.payload.value);
            sharedTermToVarName_[s] = name;
            return name;
        }
    }
    return "";
}

int LraSolver::getOrCreateInterfaceEqAuxVar(SharedTermId a, SharedTermId b) {
    SharedTermId lo = a < b ? a : b;
    SharedTermId hi = a < b ? b : a;
    uint64_t key = (static_cast<uint64_t>(lo) << 32) | static_cast<uint64_t>(hi);

    auto it = interfaceEqAuxVars_.find(key);
    if (it != interfaceEqAuxVars_.end()) return it->second;

    std::string va = getVarNameForSharedTerm(a);
    std::string vb = getVarNameForSharedTerm(b);

    if (va.empty() && vb.empty()) return -2;

    std::vector<std::pair<int, mpq_class>> terms;
    mpq_class rhs = 0;

    auto ca = va.empty() ? getConstantRationalValue(*coreIr_, *sharedTermRegistry_, a) : std::nullopt;
    auto cb = vb.empty() ? getConstantRationalValue(*coreIr_, *sharedTermRegistry_, b) : std::nullopt;

    if (!va.empty()) {
        terms.push_back({manager_.getOrCreateVar(gs_, va), mpq_class(1)});
    } else {
        if (!ca) return -1;
        rhs -= *ca;
    }

    if (!vb.empty()) {
        terms.push_back({manager_.getOrCreateVar(gs_, vb), mpq_class(-1)});
    } else {
        if (!cb) return -1;
        rhs += *cb;
    }

    int aux = gs_.addConstraint(terms, rhs);
    interfaceEqAuxVars_[key] = aux;
    return aux;
}

std::vector<SatLit>
LraSolver::assertedVarEqualityReason(SharedTermId a, SharedTermId b) const {
    if (!sharedTermRegistry_ || !coreIr_) return {};
    auto nameOf = [&](SharedTermId s) -> std::string {
        if (const auto* st = sharedTermRegistry_->get(s)) {
            if (coreIr_->get(st->coreExpr).isConst()) return "";
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

    // Aggregate asserted 2-var difference (in)equalities into an interval on
    // d = (na - nb); if pinned to 0, na = nb is entailed (covers an explicit
    // equality atom and two complementary inequalities). See LiaSolver.
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
        if (t0.second == 0 || t0.second != -t1.second) continue;
        mpq_class c0;
        if (t0.first == na && t1.first == nb)      c0 = t0.second;
        else if (t0.first == nb && t1.first == na) c0 = t1.second;
        else continue;
        Relation rel = e.value ? payload.rel : negateRelation(payload.rel);
        const mpq_class& rhs = payload.rhs.asRational();
        mpq_class bnd = rhs / c0;
        bool flip = (c0 < 0);
        auto addLower = [&](const mpq_class& v, SatLit lit) {
            if (!haveLo || v > lo) { lo = v; loLit = lit; haveLo = true; }
        };
        auto addUpper = [&](const mpq_class& v, SatLit lit) {
            if (!haveUp || v < up) { up = v; upLit = lit; haveUp = true; }
        };
        switch (rel) {
            case Relation::Eq: addLower(bnd, e.lit); addUpper(bnd, e.lit); break;
            case Relation::Leq: if (!flip) addUpper(bnd, e.lit); else addLower(bnd, e.lit); break;
            case Relation::Geq: if (!flip) addLower(bnd, e.lit); else addUpper(bnd, e.lit); break;
            default: break;  // strict bounds don't pin an equality
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

TheoryCheckResult LraSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    int aux = getOrCreateInterfaceEqAuxVar(a, b);
    if (aux == -2) {
        auto ca = getConstantRationalValue(*coreIr_, *sharedTermRegistry_, a);
        auto cb = getConstantRationalValue(*coreIr_, *sharedTermRegistry_, b);
        if (ca && cb && *ca != *cb) {
            return TheoryCheckResult::mkConflict(TheoryConflict{{reason}});
        }
        return TheoryCheckResult::consistent();
    }
    if (aux < 0) return TheoryCheckResult::consistent();

    interfaceEqualities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

TheoryCheckResult LraSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    int aux = getOrCreateInterfaceEqAuxVar(a, b);
    if (aux == -2) {
        auto ca = getConstantRationalValue(*coreIr_, *sharedTermRegistry_, a);
        auto cb = getConstantRationalValue(*coreIr_, *sharedTermRegistry_, b);
        if (ca && cb && *ca == *cb) {
            return TheoryCheckResult::mkConflict(TheoryConflict{{reason}});
        }
        return TheoryCheckResult::consistent();
    }
    if (aux < 0) return TheoryCheckResult::consistent();

    interfaceDisequalities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

// Track A (LP-duality polyhedral implied-equality probe). Per shared pair
// (a, b), assert the strict negation of (a - b) = 0 on the aux var representing
// (va - vb) and run feasibility check. If both directions are infeasible, the
// polyhedron pins (a - b) = 0 in every feasible model — a true multi-row
// Farkas implication, not just per-row chase. The simplex state is byte-
// equivalent before push and after pop on the no-emit path (RAII pop guarantee).
// The marker SatLit identifies the proof-by-contradiction probe bound so it can
// be filtered out of the emitted reasons (the marker is NOT part of the
// asserted state; leaking it into a reason would break downstream explanation).
//
// Marker SatLit = SatLit{0, true}. CaDiCaL allocates vars from 1 upward, so
// var==0 never identifies a real solver literal. The triple-overspec — also
// matching (var == aux) — is enforced at the assertion site by ensuring no
// other code path passes MARKER. The runtime assert below enforces "marker
// never in any emitted reason set" as a property invariant of this method.
bool LraSolver::tryProvePairEqualityByLpDuality(int aux, std::vector<SatLit>& outReasons) {
    static const SatLit MARKER{0, true};

    // RAII pop: even if check() throws or returns unexpectedly, pop runs.
    // CRITICAL: pop() only restores bound state — it does NOT clear
    // hasImmediateConflict_ / conflict_, which our probe's check() may have
    // populated. Without explicit clear, the next real LRA check returns a
    // STALE conflict from our probe (observed: TM gets a phantom conflict at
    // NO check #2 right after a probe emit, dropping the recovery to sat).
    // backtrackToLevel(level) clears those fields and leaves all bounds with
    // level <= the level (so it is bound-state byte-equivalent to just pop).
    struct ProbeScope {
        GeneralSimplex& gs;
        int level;
        ProbeScope(GeneralSimplex& g, int lvl) : gs(g), level(lvl) { gs.push(); }
        ~ProbeScope() { gs.pop(); gs.backtrackToLevel(level); }
        ProbeScope(const ProbeScope&) = delete;
        ProbeScope& operator=(const ProbeScope&) = delete;
    };

    auto collectAndFilter = [&](std::vector<SatLit>& out) {
        // Skip BoundReasons whose reason == MARKER — those are the probe bound
        // (proof-by-contradiction witness, not part of the asserted state).
        for (const auto& br : gs_.getConflict()) {
            if (br.reason == MARKER) continue;
            out.push_back(br.reason);
        }
    };

    std::vector<SatLit> upperReasons, lowerReasons;

    // Probe 1: assert aux <= -δ (strict aux < 0). Unsat ⇒ aux ≥ 0 in every model.
    {
        ProbeScope scope(gs_, currentLevel_);
        BoundInfo strict(BoundValue(DeltaRational(mpq_class(0), mpq_class(-1))), MARKER);
        bool ok = gs_.assertUpper(aux, strict, currentLevel_);
        bool unsat = !ok || gs_.check() == GeneralSimplex::Result::Unsat;
        if (unsat) collectAndFilter(upperReasons);
        if (!unsat) return false;
    }

    // Probe 2: assert aux >= +δ (strict aux > 0). Unsat ⇒ aux ≤ 0 in every model.
    {
        ProbeScope scope(gs_, currentLevel_);
        BoundInfo strict(BoundValue(DeltaRational(mpq_class(0), mpq_class(1))), MARKER);
        bool ok = gs_.assertLower(aux, strict, currentLevel_);
        bool unsat = !ok || gs_.check() == GeneralSimplex::Result::Unsat;
        if (unsat) collectAndFilter(lowerReasons);
        if (!unsat) return false;
    }

    // Combine + dedup. Both directions infeasible ⇒ aux pinned at 0 in every
    // feasible model, so (a - b) = 0 is implied for the pair the aux represents.
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

    // Soundness invariant: marker MUST NEVER appear in the emitted reasons.
    // This is the proof-by-contradiction probe — leaking it would cite an
    // artificial bound and break downstream explanation chains. A debug assert
    // here catches any filter regression at runtime.
    assert(std::none_of(outReasons.begin(), outReasons.end(),
        [](const SatLit& r) { return r == MARKER; }) &&
        "Track A: marker bound leaked into emitted reason set");

    return true;
}

std::vector<TheorySolver::SharedEqualityPropagation>
LraSolver::getDeducedSharedEqualities() {
    if (!sharedTermRegistry_) return {};
    // Variable-variable implied equalities: an asserted 2-var equality atom or
    // two complementary inequalities pin the difference of two shared variables
    // to 0, making them equal. Propagate to EUF so array Row1/congruence fires
    // (QF_ALRA/AUFLRA analogs of R4/e6). Sound: assertedVarEqualityReason only
    // fires on a genuine pin. Bounded by #distinct shared variables.
    std::vector<SharedTermId> sharedVars;
    for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
        if (const auto* st = sharedTermRegistry_->get(stId)) {
            if (coreIr_ && coreIr_->get(st->coreExpr).isConst()) continue;
        }
        if (getVarNameForSharedTerm(stId).empty()) continue;
        sharedVars.push_back(stId);
    }
    std::vector<TheorySolver::SharedEqualityPropagation> result;
    const int n = static_cast<int>(sharedVars.size());

    // Direct-pair edges: assertedVarEqualityReason catches both explicit
    // 2-var Eq atoms and complementary-bound pairs that pin (a - b) to 0.
    std::vector<std::vector<std::pair<int, std::vector<SatLit>>>> adj(n);
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            auto reasons = assertedVarEqualityReason(sharedVars[i], sharedVars[j]);
            if (reasons.empty()) continue;
            adj[i].push_back({j, reasons});
            adj[j].push_back({i, reasons});
            // Always emit direct pairs (current behavior).
            result.push_back(TheorySolver::SharedEqualityPropagation{
                sharedVars[i], sharedVars[j], std::move(reasons)});
        }
    }

    // Track 2b (XOLVER_SIMPLEX_IMPLIED_EQ): closure beyond per-pair direct
    // detection. Two sub-passes, deduped against each other and against the
    // direct pairs emitted above:
    //   Step 1 (transitivity): chain of asserted equalities through the
    //     shared-var graph (x=z and z=y -> x=y) — chain reasons are the union
    //     of SatLits along the BFS path. Sound by construction.
    //   Step 2 (polyhedral implied-eq): aux-var tight-bound query — for each
    //     existing interface aux var (the (a, b) pairs EUF already cares
    //     about), if the simplex bound-propagation engine pins it to 0 on
    //     BOTH sides, emit a = b with the union of lower + upper bound
    //     reasons. Sound because the engine derives bounds from tableau rows
    //     (Farkas-traceable), valid in every feasible model — not just the
    //     current vertex. Free pairs (no tight bound, no equality
    //     implication) are NOT emitted: the engine never derives a 0 bound
    //     unless the constraints force it.
    auto pairKey = [](int a, int b) -> uint64_t {
        int lo = std::min(a, b), hi = std::max(a, b);
        return (static_cast<uint64_t>(lo) << 32) | static_cast<uint32_t>(hi);
    };
    std::unordered_set<uint64_t> emittedPair;
    for (int i = 0; i < n; ++i)
        for (const auto& [j, rs] : adj[i])
            if (i < j) emittedPair.insert(pairKey(i, j));
    if (impliedEqEnabled_ && n > 2) {
        // For each shared var i, BFS the equality graph. For every shared j>i
        // reachable through a chain of >=2 edges (not already a direct edge),
        // emit eq(i,j) with the concatenated, deduped reasons of the path.
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
                // Reconstruct + dedup chain reasons.
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

    // Step 2: polyhedral implied-eq via gs_.proveFixedValue — multi-row Farkas
    // through the tableau (LIA's existing detection uses the same primitive).
    // PROACTIVELY ensure an interface aux var exists for every shared-var pair
    // (idempotent via interfaceEqAuxVars_, bounded by shared-var count which is
    // small for combination workloads). Each aux represents a (va - vb) linear
    // combination; proveFixedValue chases tableau rows recursively to discover
    // whether the constraint system pins it. If it proves the aux is fixed
    // at 0 (rational a == 0 AND delta b == 0), the polyhedron entails va = vb
    // in every feasible model — emit a = b with the collected bound reasons.
    if (impliedEqEnabled_ && n >= 2) {
        for (int i = 0; i < n; ++i)
            for (int j = i + 1; j < n; ++j)
                getOrCreateInterfaceEqAuxVar(sharedVars[i], sharedVars[j]);

        std::unordered_map<SharedTermId, int> sharedTermToIdx;
        sharedTermToIdx.reserve(sharedVars.size());
        for (int k = 0; k < n; ++k) sharedTermToIdx[sharedVars[k]] = k;

        for (const auto& [pk, aux] : interfaceEqAuxVars_) {
            if (aux < 0) continue;
            SharedTermId lo = static_cast<SharedTermId>(pk >> 32);
            SharedTermId hi = static_cast<SharedTermId>(pk & 0xFFFFFFFFu);
            auto liIt = sharedTermToIdx.find(lo);
            auto hiIt = sharedTermToIdx.find(hi);
            if (liIt == sharedTermToIdx.end() || hiIt == sharedTermToIdx.end()) continue;
            int i = liIt->second, j = hiIt->second;
            uint64_t k = pairKey(i, j);
            if (emittedPair.count(k)) continue;
            auto fixed = gs_.proveFixedValue(aux);
            if (!fixed) continue;
            // The aux's value at 0 means (va - vb) == 0 (since the constraint is
            // aux = va - vb; the aux's bound being 0 is the equality witness).
            if (!(fixed->first.a == 0 && fixed->first.b == 0)) continue;
            std::vector<SatLit> rs;
            rs.reserve(fixed->second.size());
            for (const auto& br : fixed->second) rs.push_back(br.reason);
            std::sort(rs.begin(), rs.end(),
                [](SatLit a, SatLit b) {
                    if (a.var != b.var) return a.var < b.var;
                    return a.sign < b.sign;
                });
            rs.erase(std::unique(rs.begin(), rs.end(),
                [](SatLit a, SatLit b) {
                    return a.var == b.var && a.sign == b.sign;
                }), rs.end());
            emittedPair.insert(k);
            result.push_back(TheorySolver::SharedEqualityPropagation{
                sharedVars[i], sharedVars[j], std::move(rs)});
        }

        // Step 3 / Track A: LP-duality probe — true multi-row Farkas via
        // push/assert-strict/check/pop. Catches the Wisa-style case where the
        // polyhedron pins (a - b) = 0 by a combination of 3+ inequalities that
        // doesn't bottom out via proveFixedValue. Pre-filter: skip pairs whose
        // current simplex value isn't already 0 (the polyhedron doesn't pin
        // them, so the probe would just return Sat). Budget: lpDualityBudget_
        // probes per call (each up to 2 simplex checks); 0 disables.
        int probesLeft = lpDualityBudget_;
        if (probesLeft > 0) {
            for (const auto& [pk, aux] : interfaceEqAuxVars_) {
                if (probesLeft <= 0) break;
                if (aux < 0) continue;
                SharedTermId lo = static_cast<SharedTermId>(pk >> 32);
                SharedTermId hi = static_cast<SharedTermId>(pk & 0xFFFFFFFFu);
                auto liIt = sharedTermToIdx.find(lo);
                auto hiIt = sharedTermToIdx.find(hi);
                if (liIt == sharedTermToIdx.end() || hiIt == sharedTermToIdx.end()) continue;
                int i = liIt->second, j = hiIt->second;
                uint64_t k = pairKey(i, j);
                if (emittedPair.count(k)) continue;
                // Pre-filter: current model says aux != 0 ⇒ polyhedron does not
                // pin ⇒ probe would be Sat in both directions ⇒ no emission.
                DeltaRational cur = gs_.value(aux);
                if (!(cur.a == 0 && cur.b == 0)) continue;
                std::vector<SatLit> rs;
                bool pinned = tryProvePairEqualityByLpDuality(aux, rs);
                --probesLeft;
                if (!pinned) continue;
                emittedPair.insert(k);
                result.push_back(TheorySolver::SharedEqualityPropagation{
                    sharedVars[i], sharedVars[j], std::move(rs)});
            }
        }
    }
    return result;
}

std::vector<SatLit> LraSolver::allActiveReasons() const {
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

std::optional<TheoryLemma> LraSolver::buildEntailmentLemma(
    const LraPropagationEngine::ExplainedBound& eb) const {
    auto it = auxFormInfo_.find(eb.var);
    if (it == auxFormInfo_.end()) return std::nullopt;
    const auto& info = it->second;
    mpq_class boundRhs = info.rhs + eb.value.a;

    // Sound rational reconstruction of a delta-rational bound s ~ a + bδ
    // (δ a positive infinitesimal), translated to formValue = s + rhs:
    //   lower s ≥ a+bδ :  b>0 ⇒ formValue > a (Gt);  b=0 ⇒ ≥ a (Geq);
    //                     b<0 ⇒ a+bδ is just-below a, so NO rational bound ≥ a
    //                           is sound (Geq a over-tightens) ⇒ SKIP.
    //   upper s ≤ a+bδ :  b<0 ⇒ formValue < a (Lt);  b=0 ⇒ ≤ a (Leq);
    //                     b>0 ⇒ just-above a ⇒ SKIP (Leq a over-tightens).
    // The over-tight b<0-lower / b>0-upper cases are exactly the false-UNSAT bug.
    Relation rel;
    if (eb.isLower) {
        if (eb.value.b > 0)      rel = Relation::Gt;
        else if (eb.value.b == 0) rel = Relation::Geq;
        else return std::nullopt;          // b<0 lower: not soundly representable
    } else {
        if (eb.value.b < 0)      rel = Relation::Lt;
        else if (eb.value.b == 0) rel = Relation::Leq;
        else return std::nullopt;          // b>0 upper: not soundly representable
    }

    if (!registry_) return std::nullopt;
    SatLit implied = registry_->getOrCreateLinearBoundAtom(
        info.lhs, rel, boundRhs, TheoryId::LRA);

    // Clause (¬reason₁ ∨ ... ∨ ¬reasonₖ ∨ implied): a theory tautology, since
    // the reasons Farkas-entail `implied`. Reasons are asserted-true literals,
    // so their negations sit in the clause. Drop a degenerate empty-reason
    // derivation (would be a bare unit -> not safe).
    if (eb.reasons.empty()) return std::nullopt;
    TheoryLemma lem;
    lem.kind = LemmaKind::Entailment;
    lem.lits.reserve(eb.reasons.size() + 1);
    for (SatLit r : eb.reasons) lem.lits.push_back(r.negated());
    lem.lits.push_back(implied);
    return lem;
}

std::vector<TheoryLemma> LraSolver::takeEntailmentPropagations() {
    return std::move(entailmentProps_);
}

std::optional<bool> LraSolver::evalAtomAtModel(SatVar v) {
    // Build the STATIC form once (expensive findBySatVar + payload extraction).
    auto cit = atomEvalCache_.find(v);
    if (cit == atomEvalCache_.end()) {
        AtomEvalForm form;
        const TheoryAtomRecord* rec = registry_ ? registry_->findBySatVar(v) : nullptr;
        if (rec && std::holds_alternative<LinearAtomPayload>(rec->payload)) {
            const auto& p = std::get<LinearAtomPayload>(rec->payload);
            if (p.rhs.isRational()) {
                form.isLinear = true;
                form.rel = p.rel;
                form.rhs = p.rhs.asRational().get_d();
                form.terms.reserve(p.lhs.terms.size());
                for (const auto& t : p.lhs.terms) {
                    form.terms.push_back({t.first, t.second.get_d()});
                }
            }
        }
        cit = atomEvalCache_.emplace(v, std::move(form)).first;
    }
    const AtomEvalForm& f = cit->second;
    if (!f.isLinear) return std::nullopt;

    // Resolve indices FRESH (O(1) per term). A var not yet in the simplex (or
    // gone after backtrack) -> skip O(1). Caching the name not the index keeps
    // this crash-safe under lazy registration. double arithmetic, zero alloc.
    double s = 0.0;
    for (const auto& term : f.terms) {
        int idx = manager_.findVarIndex(term.first);
        if (idx < 0) return std::nullopt;  // pending: var not registered yet
        s += term.second * gs_.value(idx).a.get_d();
    }
    switch (f.rel) {
        case Relation::Leq: return s <= f.rhs;
        case Relation::Lt:  return s <  f.rhs;
        case Relation::Geq: return s >= f.rhs;
        case Relation::Gt:  return s >  f.rhs;
        case Relation::Eq:  return s == f.rhs;
        case Relation::Neq: return s != f.rhs;
        default:            return std::nullopt;
    }
}

void LraSolver::allowInterfaceDiseqModelBranch(SharedTermId a, SharedTermId b) {
    SharedTermId lo = a < b ? a : b;
    SharedTermId hi = a < b ? b : a;
    uint64_t key = (static_cast<uint64_t>(lo) << 32) | static_cast<uint64_t>(hi);
    diseqBranchAuthorized_.insert(key);
}

std::optional<RealValue> LraSolver::sharedTermArithValue(SharedTermId s) const {
    if (!sharedTermRegistry_ || !coreIr_) return std::nullopt;
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return std::nullopt;
    const auto& expr = coreIr_->get(st->coreExpr);
    // Numeric constants carry their value directly.
    if (auto cv = getConstantRationalValue(*coreIr_, *sharedTermRegistry_, s)) {
        return RealValue::fromMpq(*cv);
    }
    if (expr.kind != Kind::Variable ||
        !std::holds_alternative<std::string>(expr.payload.value)) {
        return std::nullopt;
    }
    const std::string& name = std::get<std::string>(expr.payload.value);
    int idx = manager_.findVarIndex(name);
    if (idx < 0) return std::nullopt;
    mpq_class delta = gs_.computeSafeDelta();
    DeltaRational val = gs_.value(idx);
    mpq_class concrete = val.a + val.b * delta;
    return RealValue::fromMpq(concrete);
}

std::optional<TheorySolver::TheoryModel> LraSolver::getModel() const {
    // Instantiate the infinitesimal δ to a concrete positive rational so the
    // model is a plain rational assignment — otherwise a strict-inequality
    // value like `1/2 + 1/2δ` would leak into get-model output. Any δ in
    // (0, computeSafeDelta()] preserves all active bounds.
    mpq_class delta = gs_.computeSafeDelta();
    TheoryModel model;
    for (int i = 0; i < gs_.numVars(); ++i) {
        std::string name = manager_.getVarName(i);
        if (name.empty()) continue;
        if (name.size() >= 2 && name[0] == '_' && name[1] == '_') continue;
        DeltaRational val = gs_.value(i);
        mpq_class concrete = val.a + val.b * delta;  // a + bδ
        model.assignments[name] = concrete.get_str();
        // Typed channel carries the same concrete rational value.
        model.numericAssignments.insert({name, RealValue::fromMpq(concrete)});
    }
    if (model.assignments.empty()) return std::nullopt;
    return model;
}

#ifdef XOLVER_LRA_PROFILE
void LraSolver::ProfileStats::dump() const {
    int totalConflicts = fallbackConflictCount + immediateConflictCount + rowConflictCount;
    std::ofstream ofs("/tmp/lra_profile.log", std::ios::app);
    if (!ofs) return;
    ofs << "[LRA-PROFILE] solve=" << solveCount
        << " checks=" << checkCalls
        << " avgActive=" << (checkCalls > 0 ? totalActiveLiterals / checkCalls : 0)
        << " maxActive=" << maxActiveLiterals
        << " avgNew=" << (checkCalls > 0 ? totalNewLiterals / checkCalls : 0)
        << " assertMs=" << (assertBoundTimeUs / 1000)
        << " simplexMs=" << (simplexCheckTimeUs / 1000)
        << " fallback=" << fallbackConflictCount
        << " immediate=" << immediateConflictCount
        << " row=" << rowConflictCount
        << " avgConflictSize=" << (totalConflicts > 0 ? totalConflictSize / totalConflicts : 0)
        << " maxConflictSize=" << maxConflictSize
        << " split=" << disequalitySplitCount
        << " pivots=" << totalPivotCount
        << " mpqMs=" << (mpqOpTimeUs / 1000)
        << " maxCoeffNumBits=" << maxCoeffNumBits
        << " maxCoeffDenBits=" << maxCoeffDenBits
        << " avgCoeffNumBits=" << (totalCoeffSamples > 0 ? totalCoeffNumBits / totalCoeffSamples : 0)
        << " avgCoeffDenBits=" << (totalCoeffSamples > 0 ? totalCoeffDenBits / totalCoeffSamples : 0)
        << "\n";
}
#endif

} // namespace xolver
