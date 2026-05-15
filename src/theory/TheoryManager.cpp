#include "theory/TheoryManager.h"
#include "theory/TheoryAtomRegistry.h"
#include "theory/TheoryLemmaDatabase.h"
#include "sat/SatSolver.h"
#include <cassert>
#include <algorithm>
#include <iostream>

namespace nlcolver {

void TheoryManager::registerSolver(std::unique_ptr<TheorySolver> solver) {
    TheoryId id = solver->id();
    solvers_.push_back(std::move(solver));
    solverByTheory_[id] = solvers_.back().get();
}

void TheoryManager::clearSolvers() {
    solvers_.clear();
    solverByTheory_.clear();
    if (sharedTermRegistry_) sharedTermRegistry_->clear();
    sharedEqMgr_.clear();
    pendingSharedEqEvents_.clear();
    snapshots_.clear();
    deducedEqCache_.clear();
}

std::vector<TheorySolver*> TheoryManager::solversOwning(SharedTermId a, SharedTermId b) const {
    std::unordered_set<TheoryId> ownerSet;
    if (sharedTermRegistry_) {
        if (auto* ta = sharedTermRegistry_->get(a)) {
            for (TheoryId id : ta->owners) ownerSet.insert(id);
        }
        if (auto* tb = sharedTermRegistry_->get(b)) {
            for (TheoryId id : tb->owners) ownerSet.insert(id);
        }
    }

    std::vector<TheorySolver*> result;
    for (TheoryId id : ownerSet) {
        auto it = solverByTheory_.find(id);
        if (it != solverByTheory_.end() && it->second->supportsCombination()) {
            result.push_back(it->second);
        }
    }
    return result;
}

void TheoryManager::ensureSnapshotForLevel(int level) {
    if (snapshots_.empty() || snapshots_.back().level < level) {
        snapshots_.push_back({level, sharedEqMgr_.snapshot()});
    }
}

TheoryManager::LevelSnapshot& TheoryManager::snapshotForLevel(int level) {
    for (auto it = snapshots_.rbegin(); it != snapshots_.rend(); ++it) {
        if (it->level <= level) return *it;
    }
    static LevelSnapshot empty{0, {}};
    return empty;
}

void TheoryManager::discardSnapshotsAbove(int level) {
    while (!snapshots_.empty() && snapshots_.back().level > level) {
        snapshots_.pop_back();
    }
}

void TheoryManager::assertTheoryLit(const TheoryAtomRecord& atom,
                                    SatLit assignedLit, int level) {
    if (combinationMode_ && atom.theory == TheoryId::Combination) {
        auto& payload = std::get<SharedEqualityPayload>(atom.payload);
        SatLit reasonLit = assignedLit; // already the actual assigned literal
        pendingSharedEqEvents_.push_back({
            payload.a, payload.b,
            assignedLit.sign, // true if Eq(a,b), false if ¬Eq(a,b)
            reasonLit, level
        });
        return;
    }

    auto it = solverByTheory_.find(atom.theory);
    if (it != solverByTheory_.end()) {
        bool value = (assignedLit.var == atom.satVar && assignedLit.sign);
        it->second->assertLit(atom, value, level, assignedLit);
    }
}

void TheoryManager::backtrackToLevel(int level) {
    // Remove pending events from levels above target
    auto it = std::remove_if(
        pendingSharedEqEvents_.begin(),
        pendingSharedEqEvents_.end(),
        [level](const auto& ev) { return ev.decisionLevel > level; });
    pendingSharedEqEvents_.erase(it, pendingSharedEqEvents_.end());

    auto& snap = snapshotForLevel(level);
    sharedEqMgr_.rollback(snap.sharedEqSnap);

    for (auto& solver : solvers_) {
        solver->backtrackToLevel(level);
    }

    discardSnapshotsAbove(level);
}

TheoryCheckResult TheoryManager::check(TheoryLemmaDatabase& lemmaDb) {
    if (!combinationMode_) {
        // Legacy single-theory path
        if (solvers_.empty()) return TheoryCheckResult::consistent();
        for (auto& solver : solvers_) {
            auto tr = solver->check(lemmaDb);
            if (tr.kind != TheoryCheckResult::Kind::Consistent) {
                return tr;
            }
        }
        return TheoryCheckResult::consistent();
    }

    // ---- Nelson-Oppen combination path ----

    // 1. Process pending SAT-assigned shared equalities/disequalities
    std::cerr << "[TM] pending events=" << pendingSharedEqEvents_.size() << "\n";
    for (auto& ev : pendingSharedEqEvents_) {
        if (ev.isEquality) {
            sharedEqMgr_.assertEquality(ev.a, ev.b, ev.reasonLit);
            if (auto c = sharedEqMgr_.checkDisequalityConflict()) {
                std::cerr << "[TM] SEM conflict! size=" << c->clause.size() << " clause=";
                for (auto& l : c->clause) std::cerr << (l.sign?"":"-") << l.var << " ";
                std::cerr << "\n";
                pendingSharedEqEvents_.clear();
                return TheoryCheckResult::mkConflict(*c);
            }
            for (auto* solver : solversOwning(ev.a, ev.b)) {
                auto r = solver->assertInterfaceEquality(ev.a, ev.b, ev.reasonLit);
                if (r.kind != TheoryCheckResult::Kind::Consistent) {
                    std::cerr << "[TM] solver conflict/unknown in equality\n";
                    pendingSharedEqEvents_.clear();
                    return r;
                }
            }
        } else {
            sharedEqMgr_.assertDisequality(ev.a, ev.b, ev.reasonLit);
            if (auto c = sharedEqMgr_.checkDisequalityConflict()) {
                std::cerr << "[TM] SEM conflict! size=" << c->clause.size() << "\n";
                pendingSharedEqEvents_.clear();
                return TheoryCheckResult::mkConflict(*c);
            }
            for (auto* solver : solversOwning(ev.a, ev.b)) {
                auto r = solver->assertInterfaceDisequality(ev.a, ev.b, ev.reasonLit);
                if (r.kind != TheoryCheckResult::Kind::Consistent) {
                    std::cerr << "[TM] solver conflict/unknown in disequality\n";
                    pendingSharedEqEvents_.clear();
                    return r;
                }
            }
        }
    }
    pendingSharedEqEvents_.clear();

    // 2. Run each theory check
    for (auto& solver : solvers_) {
        auto tr = solver->check(lemmaDb);
        if (tr.kind != TheoryCheckResult::Kind::Consistent) {
            std::cerr << "[TM] solver " << (int)solver->id() << " check result=" << (int)tr.kind << "\n";
            if (tr.conflictOpt) {
                std::cerr << "[TM]  conflict clause size=" << tr.conflictOpt->clause.size() << "\n";
            }
            return tr;
        }
    }

    // 3. Collect theory-propagated shared equalities
    for (size_t i = 0; i < solvers_.size(); ++i) {
        auto* solver = solvers_[i].get();
        if (!solver->supportsCombination()) continue;
        for (auto& prop : solver->getDeducedSharedEqualities()) {
            SatLit eqLit = registry_->getOrCreateSharedEqualityAtom(prop.a, prop.b);
            if (assignmentView_) {
                LitValue val = assignmentView_->value(eqLit);
                if (val == LitValue::True) {
                    continue; // already true in current model
                }
            }

            ReportedPropKey key{solver->id(), prop.a, prop.b};
            if (deducedEqCache_.count(key)) continue;
            deducedEqCache_.insert(key);

            TheoryLemma lemma;
            for (auto& reason : prop.reasons) {
                lemma.lits.push_back(reason.negated());
            }
            lemma.lits.push_back(eqLit);
            if (lemmaDb.insertIfNew(lemma)) {
                return TheoryCheckResult::mkLemma(std::move(lemma));
            }
        }
    }

    return TheoryCheckResult::consistent();
}

} // namespace nlcolver
