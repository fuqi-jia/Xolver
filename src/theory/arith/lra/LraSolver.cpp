#include "theory/arith/lra/LraSolver.h"
#include "theory/DebugTrace.h"
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
    manager_.resetBoundReasons();
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
    interfaceDisequalities_.erase(idIt, idIt);
}

TheoryCheckResult LraSolver::check(TheoryLemmaDatabase& /*lemmaDb*/) {
    NO_DBG << "[LRA] check begin\n";
    // Rebuild all bounds from current active assignments.
    gs_.resetActiveBounds();
    manager_.resetBoundReasons();
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
        if (payload.rel == Relation::Neq) {
            disequalities_.push_back({auxVar, a.lit});
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
                tc.clause.push_back(ieq.reason.negated());
                NO_DBG << "[LRA] IEQ immediate conflict: " << debug::fmtClause(tc.clause) << "\n";
                return TheoryCheckResult::mkConflict(std::move(tc));
            }
        }
    }

    auto r = gs_.check();
    NO_DBG << "[LRA] simplex result=" << (r == GeneralSimplex::Result::Sat ? "Sat" :
                                          r == GeneralSimplex::Result::Unsat ? "Unsat" : "Unknown") << "\n";
    if (r == GeneralSimplex::Result::Unsat) {
        auto tc = manager_.translateConflict(gs_);
        NO_DBG << "[LRA] full conflict: " << debug::fmtClause(tc.clause) << "\n";
        // Augment conflict with interface equality reasons that are decisions
        // (level > 0).  Level-0 interface equalities are unit propagations;
        // including them makes the clause non-unit and causes the SAT solver
        // to backtrack instead of detecting UNSAT at level 0.
        for (const auto& ieq : interfaceEqualities_) {
            if (ieq.level > 0) {
                tc.clause.push_back(ieq.reason.negated());
            }
        }
        NO_DBG << "[LRA] augmented conflict: " << debug::fmtClause(tc.clause) << "\n";
        if (tc.clause.empty()) {
            NO_DBG << "[BUG] LRA empty conflict clause!\n";
        }
        return TheoryCheckResult::mkConflict(std::move(tc));
    }
    if (r == GeneralSimplex::Result::Unknown) {
        return TheoryCheckResult::unknown();
    }

    // Stage A: skip interface disequality checking against current model value.
    (void)interfaceDisequalities_;

    if (!disequalities_.empty()) {
        return handleDisequalities();
    }

    NO_DBG << "[LRA] Consistent\n";
    return TheoryCheckResult::consistent();
}

TheoryCheckResult LraSolver::handleDisequalities() {
    for (const auto& d : disequalities_) {
        auto val = gs_.value(d.auxVar);
        if (val.isZero()) {
            return TheoryCheckResult::mkLemma(buildDiseqSplitLemma(d));
        }
    }
    return TheoryCheckResult::consistent();
}

TheoryLemma LraSolver::buildDiseqSplitLemma(const DiseqInfo& d) {
    SatLit notD = d.lit.negated();
    SatLit lt = d.lit;
    SatLit gt = d.lit;
    (void)lt; (void)gt;
    return TheoryLemma{{notD}};
}

// ---------------------------------------------------------------------------
// Nelson-Oppen combination hooks (skeleton for Stage A)
// ---------------------------------------------------------------------------

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
    if (va.empty() || vb.empty()) return -1;

    // Build linear form: va - vb = 0
    std::vector<std::pair<int, mpq_class>> terms;
    terms.push_back({manager_.getOrCreateVar(gs_, va), mpq_class(1)});
    terms.push_back({manager_.getOrCreateVar(gs_, vb), mpq_class(-1)});

    int aux = gs_.addConstraint(terms, mpq_class(0));
    interfaceEqAuxVars_[key] = aux;
    return aux;
}

TheoryCheckResult LraSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    int aux = getOrCreateInterfaceEqAuxVar(a, b);
    if (aux < 0) return TheoryCheckResult::consistent();

    interfaceEqualities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

TheoryCheckResult LraSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    int aux = getOrCreateInterfaceEqAuxVar(a, b);
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

} // namespace nlcolver
