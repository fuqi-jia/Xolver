#include "util/MpqUtils.h"
#include "theory/arith/lra/LraSolver.h"
#include "util/MpqUtils.h"
#include "theory/combination/CareGraph.h"
#include "theory/arith/Reasoner.h"
#include "theory/core/DebugTrace.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/arith/linear/SimplexDiseqSplitter.h"
#include "theory/core/TheoryAtomTypes.h"
#include <algorithm>
#include <cassert>
#include <chrono>
#include <fstream>
#include <iostream>

namespace zolver {

LraSolver::LraSolver() {
    // Phase 2: single core reasoner (incremental replay + interface eqs +
    // simplex + disequality split + propagation).
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "lra.core",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCore(db, e); }));
}

LraSolver::~LraSolver() {
#ifdef ZOLVER_LRA_PROFILE
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
#ifdef ZOLVER_LRA_PROFILE
    if (profile_.checkCalls > 0) {
        profile_.dump();
    }
    profile_.resetForNewSolve();
#endif
    theoryTrail_.clear();
    appliedCursor_ = 0;
    pendingConflict_.reset();
    diseqBranchAuthorized_.clear();
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

#ifdef ZOLVER_LRA_PROFILE
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
#ifdef ZOLVER_LRA_PROFILE
            int sz = static_cast<int>(tc.clause.size());
            profile_.totalConflictSize += sz;
            if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
            profile_.immediateConflictCount++;
#endif
            pendingConflict_ = TheoryCheckResult::mkConflict(std::move(tc));
            return *pendingConflict_;
        }
    }

#ifdef ZOLVER_LRA_PROFILE
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
#ifdef ZOLVER_LRA_PROFILE
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

#ifdef ZOLVER_LRA_PROFILE
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
#ifdef ZOLVER_LRA_PROFILE
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
#ifdef ZOLVER_LRA_PROFILE
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
    // Phase C: bound propagation
    // -------------------------------------------------------------------------
    {
        auto derived = propagationEngine_.propagateAll(gs_);
        int emitted = 0;
        const int MAX_PROPAGATION_LEMMAS = 8;
        for (const auto& eb : derived) {
            if (emitted >= MAX_PROPAGATION_LEMMAS) break;
            auto lemmaOpt = tryConvertDerivedBound(eb);
            if (lemmaOpt) {
                if (!lemmaDb.contains(*lemmaOpt)) {
                    lemmaDb.insertIfNew(*lemmaOpt);
                    ++emitted;
                }
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
#ifdef ZOLVER_LRA_PROFILE
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
    for (size_t i = 0; i < sharedVars.size(); ++i) {
        for (size_t j = i + 1; j < sharedVars.size(); ++j) {
            // Care-graph prune (ZOLVER_COMB_CAREGRAPH): only propagate an
            // implied equality to EUF if some theory cares about the pair (a
            // UF/array arg or Eq/Distinct operand). Skipping an inert pair loses
            // nothing EUF could use, and not propagating a fact never creates a
            // conflict, so it cannot cause a wrong UNSAT.
            if (careGraph_ && !careGraph_->caresPair(sharedVars[i], sharedVars[j]))
                continue;
            auto reasons = assertedVarEqualityReason(sharedVars[i], sharedVars[j]);
            if (reasons.empty()) continue;
            result.push_back(TheorySolver::SharedEqualityPropagation{
                sharedVars[i], sharedVars[j], std::move(reasons)});
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

std::optional<TheoryLemma> LraSolver::tryConvertDerivedBound(
    const LraPropagationEngine::ExplainedBound& eb) const {
    auto it = auxFormInfo_.find(eb.var);
    if (it == auxFormInfo_.end()) return std::nullopt;

    const auto& info = it->second;
    mpq_class boundRhs = info.rhs + eb.value.a;

    Relation rel;
    if (eb.isLower) {
        rel = (eb.value.b > 0) ? Relation::Gt : Relation::Geq;
    } else {
        rel = (eb.value.b < 0) ? Relation::Lt : Relation::Leq;
    }

    if (!registry_) return std::nullopt;
    SatLit lit = registry_->getOrCreateLinearBoundAtom(
        info.lhs, rel, boundRhs, TheoryId::LRA);
    return TheoryLemma{{lit}};
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

#ifdef ZOLVER_LRA_PROFILE
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

} // namespace zolver
