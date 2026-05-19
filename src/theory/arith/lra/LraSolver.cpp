#include "theory/arith/lra/LraSolver.h"
#include "theory/core/DebugTrace.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/arith/linear/SimplexDiseqSplitter.h"
#include <algorithm>
#include <cassert>
#include <chrono>
#include <fstream>
#include <iostream>

namespace nlcolver {

LraSolver::LraSolver() = default;

LraSolver::~LraSolver() {
#ifdef NLCOLVER_LRA_PROFILE
    if (profile_.checkCalls > 0) {
        profile_.dump();
    }
#endif
}

void LraSolver::push() {
    gs_.push();
}

void LraSolver::pop(uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) {
        gs_.pop();
    }
}

void LraSolver::reset() {
#ifdef NLCOLVER_LRA_PROFILE
    if (profile_.checkCalls > 0) {
        profile_.dump();
    }
    profile_.resetForNewSolve();
#endif
    theoryTrail_.clear();
    appliedCursor_ = 0;
    pendingConflict_.reset();
    gs_.resetActiveBounds();
}

void LraSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) {
    if (!std::holds_alternative<LinearAtomPayload>(atom.payload)) return;

    const auto& payload = std::get<LinearAtomPayload>(atom.payload);
    int auxVar = manager_.getOrCreateAuxVar(gs_, payload.lhs, payload.rhs);

    for (auto& e : theoryTrail_) {
        if (e.atom.satVar == atom.satVar) {
            e = {level, assertedLit, atom, value, auxVar};
            return;
        }
    }
    theoryTrail_.push_back({level, assertedLit, atom, value, auxVar});
}

void LraSolver::backtrackToLevel(int level) {
    currentLevel_ = level;

    // Backtrack GeneralSimplex bounds by SAT decision level.
    gs_.backtrackToLevel(level);

    // Synchronize theory trail.
    while (!theoryTrail_.empty() && theoryTrail_.back().level > level) {
        theoryTrail_.pop_back();
    }
    if (appliedCursor_ > theoryTrail_.size()) {
        appliedCursor_ = theoryTrail_.size();
    }

    // Interface equalities / disequalities
    auto ieIt = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceEqualities_.erase(ieIt, interfaceEqualities_.end());

    auto idIt = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceDisequalities_.erase(idIt, interfaceDisequalities_.end());

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

TheoryCheckResult LraSolver::check(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    NO_DBG << "[LRA] check begin\n";

#ifdef NLCOLVER_LRA_PROFILE
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
#ifdef NLCOLVER_LRA_PROFILE
            int sz = static_cast<int>(tc.clause.size());
            profile_.totalConflictSize += sz;
            if (sz > profile_.maxConflictSize) profile_.maxConflictSize = sz;
            profile_.immediateConflictCount++;
#endif
            pendingConflict_ = TheoryCheckResult::mkConflict(std::move(tc));
            return *pendingConflict_;
        }
    }

#ifdef NLCOLVER_LRA_PROFILE
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
#ifdef NLCOLVER_LRA_PROFILE
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

#ifdef NLCOLVER_LRA_PROFILE
    auto prof_t3 = std::chrono::steady_clock::now();
    profile_.simplexCheckTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t3 - prof_t2).count();
    profile_.totalPivotCount += gs_.pivotCount();
    gs_.resetPivotCount();
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
            NO_DBG << "[LRA] simplex conflict: " << tc.clause.size() << " lits\n";
#ifdef NLCOLVER_LRA_PROFILE
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
#ifdef NLCOLVER_LRA_PROFILE
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

    // Stage A: skip interface disequality checking against current model value.
    (void)interfaceDisequalities_;

    // -------------------------------------------------------------------------
    // Disequalities: collect from active trail entries
    // -------------------------------------------------------------------------
    std::vector<DiseqInfo> disequalities;
    for (const auto& e : theoryTrail_) {
        const auto& payload = std::get<LinearAtomPayload>(e.atom.payload);
        Relation effectiveRel = e.value ? payload.rel : negateRelation(payload.rel);
        if (effectiveRel == Relation::Neq) {
            disequalities.push_back({e.auxVar, payload.lhs, payload.rhs, e.lit});
        }
    }

    if (!disequalities.empty()) {
#ifdef NLCOLVER_LRA_PROFILE
        profile_.disequalitySplitCount++;
#endif
        return handleSimplexDisequalities(
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
            return mpq_class(*str);
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
        rhs += *ca;
    }

    if (!vb.empty()) {
        terms.push_back({manager_.getOrCreateVar(gs_, vb), mpq_class(-1)});
    } else {
        if (!cb) return -1;
        rhs -= *cb;
    }

    int aux = gs_.addConstraint(terms, rhs);
    interfaceEqAuxVars_[key] = aux;
    return aux;
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
    return {};
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

std::optional<TheorySolver::TheoryModel> LraSolver::getModel() const {
    TheoryModel model;
    for (int i = 0; i < gs_.numVars(); ++i) {
        std::string name = manager_.getVarName(i);
        if (name.empty()) continue;
        if (name.size() >= 2 && name[0] == '_' && name[1] == '_') continue;
        DeltaRational val = gs_.value(i);
        if (val.b == 0) {
            model.assignments[name] = val.a.get_str();
        } else {
            model.assignments[name] = val.toString();
        }
    }
    if (model.assignments.empty()) return std::nullopt;
    return model;
}

#ifdef NLCOLVER_LRA_PROFILE
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
        << "\n";
}
#endif

} // namespace nlcolver
