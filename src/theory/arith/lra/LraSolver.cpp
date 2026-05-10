#include "theory/arith/lra/LraSolver.h"
#include <cassert>

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

void LraSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) {
    if (!std::holds_alternative<LinearAtomPayload>(atom.payload)) return;

    for (auto& a : activeAssignments_) {
        if (a.atom.satVar == atom.satVar) {
            a = {level, reason, atom, value};
            return;
        }
    }
    activeAssignments_.push_back({level, reason, atom, value});
}

void LraSolver::backtrackToLevel(int level) {
    auto it = std::remove_if(activeAssignments_.begin(), activeAssignments_.end(),
        [level](const auto& a) { return a.level > level; });
    activeAssignments_.erase(it, activeAssignments_.end());
}

TheoryCheckResult LraSolver::check(TheoryLemmaDatabase& /*lemmaDb*/) {
    // Rebuild all bounds from current active assignments.
    gs_.resetActiveBounds();
    manager_.resetBoundReasons();
    disequalities_.clear();

    for (const auto& a : activeAssignments_) {
        const auto& payload = std::get<LinearAtomPayload>(a.atom.payload);
        int auxVar = manager_.getOrCreateAuxVar(gs_, payload.lhs, payload.rhs);
        if (payload.rel == Relation::Neq) {
            disequalities_.push_back({auxVar, a.lit});
        } else {
            bool ok = manager_.assertBound(gs_, auxVar, payload.rel, a.value, a.lit, a.level);
            if (!ok) {
                return TheoryCheckResult::mkConflict(manager_.translateConflict(gs_));
            }
        }
    }

    auto r = gs_.check();
    if (r == GeneralSimplex::Result::Unsat) {
        return TheoryCheckResult::mkConflict(manager_.translateConflict(gs_));
    }
    if (r == GeneralSimplex::Result::Unknown) {
        return TheoryCheckResult::unknown();
    }

    if (!disequalities_.empty()) {
        return handleDisequalities();
    }

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

} // namespace nlcolver
