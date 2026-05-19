#include "theory/arith/lra/LraSolver.h"
#include "theory/DebugTrace.h"
#include "theory/TheoryAtomRegistry.h"
#include "theory/TheoryLemmaDatabase.h"
#include <algorithm>
#include <cassert>
#include <iostream>

namespace nlcolver {

LraSolver::LraSolver() = default;

void LraSolver::push() {
    gs_.push();
}

void LraSolver::pop(uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) {
        gs_.pop();
    }
}

void LraSolver::reset() {
    activeAssignments_.clear();
    gs_.resetActiveBounds();
}

void LraSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) {
    if (!std::holds_alternative<LinearAtomPayload>(atom.payload)) return;

    for (auto& a : activeAssignments_) {
        if (a.atom.satVar == atom.satVar) {
            a = {level, assertedLit, atom, value};
            return;
        }
    }
    activeAssignments_.push_back({level, assertedLit, atom, value});
}

void LraSolver::backtrackToLevel(int level) {
    currentLevel_ = level;
    auto it = std::remove_if(activeAssignments_.begin(), activeAssignments_.end(),
        [level](const auto& a) { return a.level > level; });
    activeAssignments_.erase(it, activeAssignments_.end());

    auto ieIt = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceEqualities_.erase(ieIt, interfaceEqualities_.end());

    auto idIt = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceDisequalities_.erase(idIt, interfaceDisequalities_.end());
}

TheoryCheckResult LraSolver::check(TheoryLemmaDatabase& lemmaDb, TheoryEffort) {
    NO_DBG << "[LRA] check begin\n";
    // Rebuild all bounds from current active assignments.
    gs_.resetActiveBounds();
    disequalities_.clear();

    NO_DBG << "[LRA] activeAssignments=" << activeAssignments_.size() << "\n";
    for (const auto& a : activeAssignments_) {
        const auto& payload = std::get<LinearAtomPayload>(a.atom.payload);
        int auxVar = manager_.getOrCreateAuxVar(gs_, payload.lhs, payload.rhs);
        NO_DBG << "[LRA] assert bound aux=" << auxVar
               << " rel=" << (int)payload.rel
               << " val=" << a.value
               << " lit=" << debug::fmtLit(a.lit)
               << " level=" << a.level << "\n";
        Relation effectiveRel = a.value ? payload.rel : negateRelation(payload.rel);
        if (effectiveRel == Relation::Neq) {
            disequalities_.push_back({auxVar, payload.lhs, payload.rhs, a.lit});
        } else {
            bool ok = manager_.assertBound(gs_, auxVar, payload.rel, a.value, a.lit, a.level);
            if (!ok) {
                auto tc = manager_.translateConflict(gs_);
                NO_DBG << "[LRA] immediate conflict: " << debug::fmtClause(tc.clause) << "\n";
                return TheoryCheckResult::mkConflict(std::move(tc));
            }
        }
    }

    // Apply interface equalities from Nelson-Oppen combination
    NO_DBG << "[LRA] interfaceEqualities=" << interfaceEqualities_.size() << "\n";
    for (const auto& ieq : interfaceEqualities_) {
        int aux = getOrCreateInterfaceEqAuxVar(ieq.a, ieq.b);
        NO_DBG << "[LRA] IEQ st" << ieq.a << " = st" << ieq.b
               << " aux=" << aux
               << " reason=" << debug::fmtLit(ieq.reason)
               << " level=" << ieq.level << "\n";
        if (aux >= 0) {
            bool ok = true;
            ok = gs_.assertLower(aux, BoundInfo(BoundValue(DeltaRational(0)), ieq.reason)) && ok;
            ok = gs_.assertUpper(aux, BoundInfo(BoundValue(DeltaRational(0)), ieq.reason)) && ok;
            if (!ok) {
                auto tc = manager_.translateConflict(gs_);
                tc.clause.push_back(ieq.reason);
                NO_DBG << "[LRA] IEQ immediate conflict reasons: " << debug::fmtClause(tc.clause) << "\n";
                return TheoryCheckResult::mkConflict(std::move(tc));
            }
        }
    }

    auto r = gs_.check();
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
        } else {
            tc.clause = allActiveReasons();
            NO_DBG << "[LRA] fallback conflict (allActiveReasons): " << tc.clause.size() << " lits\n";
        }
        return TheoryCheckResult::mkConflict(std::move(tc));
    }
    if (r == GeneralSimplex::Result::Unknown) {
        return TheoryCheckResult::unknown();
    }

    // Stage A: skip interface disequality checking against current model value.
    (void)interfaceDisequalities_;

    if (!disequalities_.empty()) {
        return handleDisequalities(lemmaDb);
    }

    NO_DBG << "[LRA] Consistent\n";
    return TheoryCheckResult::consistent();
}

TheoryCheckResult LraSolver::handleDisequalities(TheoryLemmaDatabase& lemmaDb) {
    for (const auto& d : disequalities_) {
        auto val = gs_.value(d.auxVar);
        if (val.isZero()) {
            auto lemma = buildDiseqSplitLemma(d);
            if (!lemma.lits.empty()) {
                if (lemmaDb.contains(lemma)) {
                    return TheoryCheckResult::unknown();
                }
                lemmaDb.insertIfNew(lemma);
                return TheoryCheckResult::mkLemma(std::move(lemma));
            }
            return TheoryCheckResult::unknown();
        }
    }
    return TheoryCheckResult::consistent();
}

TheoryLemma LraSolver::buildDiseqSplitLemma(const DiseqInfo& d) {
    if (!registry_) return TheoryLemma{};

    auto litLt = registry_->getOrCreateLinearBoundAtom(d.lhs, Relation::Lt, d.rhs, TheoryId::LRA);
    auto litGt = registry_->getOrCreateLinearBoundAtom(d.lhs, Relation::Gt, d.rhs, TheoryId::LRA);

    TheoryLemma lemma;
    lemma.lits.push_back(d.lit.negated());
    lemma.lits.push_back(litLt);
    lemma.lits.push_back(litGt);
    return lemma;
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

    // If both sides are constants, no auxiliary variable is needed.
    // The caller (assertInterfaceEquality / assertInterfaceDisequality)
    // will detect the conflict directly.
    if (va.empty() && vb.empty()) return -2;

    // At least one side is a variable.
    // We want to encode: va - vb = 0, i.e. va = vb.
    // addConstraint(terms, rhs) creates s = sum(c_i * x_i) - rhs,
    // and assertLower/Upper(s,0) forces s = 0, so sum(c_i * x_i) = rhs.
    std::vector<std::pair<int, mpq_class>> terms;
    mpq_class rhs = 0;

    auto ca = va.empty() ? getConstantRationalValue(*coreIr_, *sharedTermRegistry_, a) : std::nullopt;
    auto cb = vb.empty() ? getConstantRationalValue(*coreIr_, *sharedTermRegistry_, b) : std::nullopt;

    if (!va.empty()) {
        // va is a variable, coefficient +1
        terms.push_back({manager_.getOrCreateVar(gs_, va), mpq_class(1)});
    } else {
        // va is constant ca: contributes +ca to RHS
        if (!ca) return -1;
        rhs += *ca;
    }

    if (!vb.empty()) {
        // vb is a variable, coefficient -1
        terms.push_back({manager_.getOrCreateVar(gs_, vb), mpq_class(-1)});
    } else {
        // vb is constant cb: contributes -cb to RHS
        // because va - cb = 0  =>  va = cb  =>  terms={(va,1)}, rhs=cb
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
        // Both sides are constants: check if they are equal.
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
        // Both sides are constants: check if they are distinct.
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
    // Stage A: return empty for now.
    // Full implementation would scan tight bounds after check().
    return {};
}

std::vector<SatLit> LraSolver::allActiveReasons() const {
    std::vector<SatLit> rs;
    rs.reserve(activeAssignments_.size() + interfaceEqualities_.size() + interfaceDisequalities_.size());
    for (const auto& a : activeAssignments_) {
        rs.push_back(a.lit);
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

} // namespace nlcolver
