#include "base/RuntimeConfig.h"
#include "ir/NumericLiteral.h"
#include "base/MpqUtils.h"
#include "applications/smt/qflra/LraSolver.h"
#include "base/MpqUtils.h"
#include "base/EnvParam.h"
#include "search/arith/Reasoner.h"
#include "contracts/DebugTrace.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "search/linear/SimplexDiseqSplitter.h"
#include "contracts/TheoryAtomTypes.h"
#ifdef XOLVER_ENABLE_PROOFS
#include "evidence/TheoryProofSink.h"
#endif
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <iostream>

namespace xolver {

static std::optional<mpq_class> getConstantRationalValue(
    const NativeTerms& ir, const SharedTermRegistry& reg, SharedTermId s);

LraSolver::LraSolver() {
    // Phase 2: single core reasoner (incremental replay + interface eqs +
    // simplex + disequality split + propagation).
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "lra.core",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCore(db, e); }));

}

LraSolver::~LraSolver() {
#ifdef XOLVER_LRA_PROFILE
    if (profile_.checkCalls > 0) {
        profile_.dump();
    }
#endif
}

#ifdef XOLVER_ENABLE_PROOFS
void LraSolver::pushLraFarkasCert() {
    // Proof certificate (proof-mode only): record the conflict atoms (by IR id)
    // and the Farkas multipliers GeneralSimplex captured for them — unit for an
    // immediate conflict, the |row coefficients| for a row conflict. Summing
    // multiplier_i * bound_i cancels the variables and leaves a constant
    // contradiction (Farkas' lemma + the infeasible-row invariant), so la_generic
    // refutes. The Solver applies the final soundness guard + Carcara checks the
    // multipliers, so a wrong cert is rejected offline, never claimed.
    auto* sink = proof::activeProofSink();
    if (!sink || !registry_) return;
    const auto& conflict = gs_.getConflict();
    const auto& coeffs = gs_.getConflictCoeffs();
    if (conflict.empty() || conflict.size() != coeffs.size()) return;
    proof::TheoryConflictCert cert;
    cert.rule = "la_generic";
    for (size_t i = 0; i < conflict.size(); ++i) {
        const TheoryAtomRecord* rec = registry_->findBySatVar(conflict[i].reason.var);
        if (!rec) return;  // can't identify the atom -> emit none (skeleton)
        cert.lits.push_back({rec->exprId, conflict[i].reason.sign});
        cert.args.push_back(coeffs[i].get_str());  // rational Farkas multiplier
    }
    if (!cert.lits.empty()) sink->addConflict(std::move(cert));
}
#endif

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
#ifdef XOLVER_ENABLE_PROOFS
            pushLraFarkasCert();
#endif
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
#ifdef XOLVER_ENABLE_PROOFS
            pushLraFarkasCert();
#endif
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

    // Lift explained row bounds to SAT as entailment clauses.
    auto derived = propagationEngine_.propagateAll(gs_);
    const int kMaxProps = 64;
    for (const auto& eb : derived) {
        if (static_cast<int>(entailmentProps_.size()) >= kMaxProps) break;
        if (auto lem = buildEntailmentLemma(eb)) {
            entailmentProps_.push_back(std::move(*lem));
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
        // Refute an interface disequality when tableau bounds pin its difference.
        if (eqReasons.empty()) {
            int aux = getOrCreateInterfaceEqAuxVar(ieq.a, ieq.b);
            if (aux >= 0) {
                auto fixed = gs_.proveFixedValue(aux);
                if (fixed && fixed->first.a == 0 && fixed->first.b == 0) {
                    for (const auto& br : fixed->second)
                        eqReasons.push_back(br.reason);
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
    // Every decided interface disequality is a semantic obligation, including
    // variable/constant pairs and pairs not created by arrangement guessing.
    // At Full effort, refine any simplex point that still equates its sides.
    if (effort == TheoryEffort::Full && registry_) {
        for (const auto& ieq : interfaceDisequalities_) {
            std::string va = getVarNameForSharedTerm(ieq.a);
            std::string vb = getVarNameForSharedTerm(ieq.b);
            int aux = getOrCreateInterfaceEqAuxVar(ieq.a, ieq.b);
            if (aux < 0) continue;
            DeltaRational d = gs_.value(aux);
            if (!(d.a == 0 && d.b == 0)) continue;  // model already separates them
            NO_DBG << "[LRA-DISEQ-BRANCH] " << va << " != " << vb
                   << " but model equates them; branching\n";
            LinearFormKey form;
            mpq_class rhs = 0;
            if (!va.empty()) form.terms.push_back({va, mpq_class(1)});
            else {
                auto c = getConstantRationalValue(*nativeTerms_, *sharedTermRegistry_, ieq.a);
                if (!c) return TheoryCheckResult::unknown("LRA unsupported interface disequality");
                rhs -= *c;
            }
            if (!vb.empty()) form.terms.push_back({vb, mpq_class(-1)});
            else {
                auto c = getConstantRationalValue(*nativeTerms_, *sharedTermRegistry_, ieq.b);
                if (!c) return TheoryCheckResult::unknown("LRA unsupported interface disequality");
                rhs += *c;
            }
            SatLit litLt = registry_->getOrCreateLinearBoundAtom(
                form, Relation::Lt, rhs, TheoryId::LRA);
            SatLit litGt = registry_->getOrCreateLinearBoundAtom(
                form, Relation::Gt, rhs, TheoryId::LRA);
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

static std::optional<mpq_class> getConstantRationalValue(const NativeTerms& ir, const SharedTermRegistry& reg, SharedTermId s) {
    const auto* term = reg.get(s);
    return term ? numericLiteral(ir, term->nativeExpr) : std::nullopt;
}

std::string LraSolver::getVarNameForSharedTerm(SharedTermId s) {
    auto it = sharedTermToVarName_.find(s);
    if (it != sharedTermToVarName_.end()) return it->second;

    if (!sharedTermRegistry_ || !nativeTerms_) return "";
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return "";

    const auto& expr = nativeTerms_->get(st->nativeExpr);
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

    auto ca = va.empty() ? getConstantRationalValue(*nativeTerms_, *sharedTermRegistry_, a) : std::nullopt;
    auto cb = vb.empty() ? getConstantRationalValue(*nativeTerms_, *sharedTermRegistry_, b) : std::nullopt;

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
    if (!sharedTermRegistry_ || !nativeTerms_) return {};
    auto nameOf = [&](SharedTermId s) -> std::string {
        if (const auto* st = sharedTermRegistry_->get(s)) {
            if (nativeTerms_->get(st->nativeExpr).isConst()) return "";
            auto it = sharedTermToVarName_.find(s);
            if (it != sharedTermToVarName_.end()) return it->second;
            const auto& e = nativeTerms_->get(st->nativeExpr);
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
        auto ca = getConstantRationalValue(*nativeTerms_, *sharedTermRegistry_, a);
        auto cb = getConstantRationalValue(*nativeTerms_, *sharedTermRegistry_, b);
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
        auto ca = getConstantRationalValue(*nativeTerms_, *sharedTermRegistry_, a);
        auto cb = getConstantRationalValue(*nativeTerms_, *sharedTermRegistry_, b);
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
            if (nativeTerms_ && nativeTerms_->get(st->nativeExpr).isConst()) continue;
        }
        if (getVarNameForSharedTerm(stId).empty()) continue;
        sharedVars.push_back(stId);
    }
    std::vector<TheorySolver::SharedEqualityPropagation> result;
    const int n = static_cast<int>(sharedVars.size());

    // iter-96 perf: assertedVarEqualityReason previously walked the ENTIRE
    // theoryTrail_ for every pair (i,j), giving O(N² × |trail|) total cost.
    // Pre-index the trail's 2-var linear non-diseq entries by sorted (n1,n2)
    // name pair ONCE; the inner loop then does O(1) map lookup + iterate
    // only the relevant entries. Soundness: the per-pair aggregation logic
    // (lo/up tracking with rel/coeff sign handling) is identical to the
    // original assertedVarEqualityReason; only the trail-scan is reorganized.
    //
    // Mirrors iter-95 7f187e6 EUF pre-interning fix — same anti-pattern of
    // "redundant per-pair work over a shared corpus" that the LIA iter-13
    // 161b4af fix first taxonomized.
    struct TwoVarEntry {
        std::string n0, n1;   // term variable names (n0 < n1 sorted)
        mpq_class c0;          // coefficient on n0 (c1 = -c0)
        Relation rel;
        mpq_class rhs;
        SatLit lit;
    };
    std::map<std::pair<std::string, std::string>, std::vector<TwoVarEntry>> twoVarIndex;
    for (const auto& e : theoryTrail_) {
        if (e.isDiseq) continue;
        if (!std::holds_alternative<LinearAtomPayload>(e.atom.payload)) continue;
        const auto& payload = std::get<LinearAtomPayload>(e.atom.payload);
        if (payload.lhs.terms.size() != 2) continue;
        const auto& t0 = payload.lhs.terms[0];
        const auto& t1 = payload.lhs.terms[1];
        if (t0.second == 0 || t0.second != -t1.second) continue;
        Relation rel = e.value ? payload.rel : negateRelation(payload.rel);
        std::string a = t0.first, b = t1.first;
        if (a > b) {
            std::swap(a, b);
            twoVarIndex[{a, b}].push_back({a, b, t1.second, rel, payload.rhs.asRational(), e.lit});
        } else {
            twoVarIndex[{a, b}].push_back({a, b, t0.second, rel, payload.rhs.asRational(), e.lit});
        }
    }

    // Cache shared term names once (was O(N) lookups inside O(N²) loop).
    std::vector<std::string> sharedNames(n);
    for (int i = 0; i < n; ++i) {
        sharedNames[i] = getVarNameForSharedTerm(sharedVars[i]);
    }

    // Direct-pair edges: assertedVarEqualityReason catches both explicit
    // 2-var Eq atoms and complementary-bound pairs that pin (a - b) to 0.
    // Perf: instead of the O(N^2) shared-var pair loop (each doing a map lookup
    // into twoVarIndex), iterate the index entries directly — O(#2-var atoms),
    // which is what actually bounds the pinned pairs. Map each index key (a name
    // pair) back to shared-var indices, aggregate the lo/up bound ONCE per key
    // (math identical to the per-pair version), and collect the pinned pairs. We
    // then emit in the SAME lexicographic (i<j) order the old loop produced, so
    // Indexing avoids repeatedly scanning the trail for each shared pair.
    std::unordered_map<std::string, std::vector<int>> nameToIdxs;
    nameToIdxs.reserve(static_cast<size_t>(n));
    for (int i = 0; i < n; ++i) {
        if (!sharedNames[i].empty()) nameToIdxs[sharedNames[i]].push_back(i);
    }
    std::vector<std::tuple<int, int, std::vector<SatLit>>> pinned;  // (i<j, reasons)
    for (const auto& [keyPair, entries] : twoVarIndex) {
        const std::string& ka = keyPair.first;
        const std::string& kb = keyPair.second;
        if (ka == kb) continue;
        auto ia = nameToIdxs.find(ka);
        auto ib = nameToIdxs.find(kb);
        if (ia == nameToIdxs.end() || ib == nameToIdxs.end()) continue;  // not both shared

        bool haveLo = false, haveUp = false;
        mpq_class lo = 0, up = 0;
        SatLit loLit{}, upLit{};
        auto addLower = [&](const mpq_class& v, SatLit lit) {
            if (!haveLo || v > lo) { lo = v; loLit = lit; haveLo = true; }
        };
        auto addUpper = [&](const mpq_class& v, SatLit lit) {
            if (!haveUp || v < up) { up = v; upLit = lit; haveUp = true; }
        };
        for (const auto& te : entries) {
            // Index entries are stored with n0 < n1 sorted (== ka < kb).
            mpq_class c0;
            if (te.n0 == ka && te.n1 == kb) c0 = te.c0;
            else if (te.n0 == kb && te.n1 == ka) c0 = -te.c0;
            else continue;  // shouldn't happen given the canonical sort
            mpq_class bnd = te.rhs / c0;
            bool flip = (c0 < 0);
            switch (te.rel) {
                case Relation::Eq: addLower(bnd, te.lit); addUpper(bnd, te.lit); break;
                case Relation::Leq: if (!flip) addUpper(bnd, te.lit); else addLower(bnd, te.lit); break;
                case Relation::Geq: if (!flip) addLower(bnd, te.lit); else addUpper(bnd, te.lit); break;
                default: break;
            }
        }
        if (!(haveLo && haveUp && lo == 0 && up == 0)) continue;
        std::vector<SatLit> reasons;
        reasons.push_back(loLit);
        if (!(upLit == loLit)) reasons.push_back(upLit);
        // idx[ka] and idx[kb] are disjoint (ka != kb), so every (i,j) is distinct.
        for (int i : ia->second) {
            for (int j : ib->second) {
                if (i == j) continue;
                pinned.emplace_back(std::min(i, j), std::max(i, j), reasons);
            }
        }
    }
    std::sort(pinned.begin(), pinned.end(),
              [](const auto& x, const auto& y) {
                  if (std::get<0>(x) != std::get<0>(y)) return std::get<0>(x) < std::get<0>(y);
                  return std::get<1>(x) < std::get<1>(y);
              });
    for (auto& [i, j, reasons] : pinned) {
        result.push_back(TheorySolver::SharedEqualityPropagation{
            sharedVars[i], sharedVars[j], std::move(reasons)});
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
    if (!registry_ || eb.reasons.empty()) return std::nullopt;
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

    // Ordinary theory propagation projects mathematical facts onto the
    // registered SAT vocabulary. Creating an atom for every intermediate
    // rational endpoint feeds fresh atoms back into propagation indefinitely.
    // Cut/split algorithms use the explicit registration interface separately.
    const auto implied = registry_->findLinearLiteral(info.lhs, rel, boundRhs);
    if (!implied || std::find(eb.reasons.begin(), eb.reasons.end(), *implied) != eb.reasons.end())
        return std::nullopt;

    // Clause (¬reason₁ ∨ ... ∨ ¬reasonₖ ∨ implied): a theory tautology, since
    // the reasons Farkas-entail `implied`. Reasons are asserted-true literals,
    // so their negations sit in the clause. Drop a degenerate empty-reason
    // derivation (would be a bare unit -> not safe).
    TheoryLemma lem;
    lem.kind = LemmaKind::Entailment;
    lem.lits.reserve(eb.reasons.size() + 1);
    for (SatLit r : eb.reasons) lem.lits.push_back(r.negated());
    lem.lits.push_back(*implied);
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

std::optional<RealValue> LraSolver::sharedTermArithValue(SharedTermId s) const {
    if (!sharedTermRegistry_ || !nativeTerms_) return std::nullopt;
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return std::nullopt;
    const auto& expr = nativeTerms_->get(st->nativeExpr);
    // Numeric constants carry their value directly.
    if (auto cv = getConstantRationalValue(*nativeTerms_, *sharedTermRegistry_, s)) {
        return RealValue::fromMpq(*cv);
    }
    if (expr.kind != Kind::Variable ||
        !std::holds_alternative<std::string>(expr.payload.value)) {
        return std::nullopt;
    }
    const std::string& name = std::get<std::string>(expr.payload.value);
    int idx = manager_.findVarIndex(name);
    if (idx < 0) return std::nullopt;
    mpq_class delta = modelDelta();
    DeltaRational val = gs_.value(idx);
    mpq_class concrete = val.a + val.b * delta;
    return RealValue::fromMpq(concrete);
}

mpq_class LraSolver::modelDelta() const {
    mpq_class delta = gs_.computeSafeDelta();
    auto preserveNonzero = [&](int aux) {
        const auto value = gs_.value(aux);
        if (value.b == 0) return;
        const mpq_class root = -value.a / value.b;
        // Every positive delta below this root preserves the symbolic sign.
        // Shrinking also preserves all simplex bounds and earlier exclusions.
        if (root > 0 && delta >= root) delta = root / 2;
    };
    for (const auto& d : activeDisequalities_) preserveNonzero(d.auxVar);
    for (const auto& d : interfaceDisequalities_) {
        const auto lo = std::min(d.a, d.b), hi = std::max(d.a, d.b);
        const uint64_t key = (static_cast<uint64_t>(lo) << 32) | hi;
        const auto found = interfaceEqAuxVars_.find(key);
        if (found != interfaceEqAuxVars_.end()) preserveNonzero(found->second);
    }
    return delta;
}

std::optional<TheorySolver::TheoryModel> LraSolver::getModel() const {
    // Instantiate the infinitesimal δ to a concrete positive rational so the
    // model is a plain rational assignment — otherwise a strict-inequality
    // value like `1/2 + 1/2δ` would leak into get-model output. Any δ in
    // (0, computeSafeDelta()] preserves bounds; modelDelta also avoids the
    // finitely many roots forbidden by ordinary/interface disequalities.
    mpq_class delta = modelDelta();
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
