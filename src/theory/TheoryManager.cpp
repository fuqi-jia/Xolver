#include "theory/TheoryManager.h"
#include "theory/TheoryAtomRegistry.h"
#include "theory/TheoryLemmaDatabase.h"
#include "theory/DebugTrace.h"
#include "sat/SatSolver.h"
#include <cassert>
#include <algorithm>
#include <iostream>

namespace nlcolver {

static int noDebugModelCheckId = 0;

static std::string stName(const SharedTermRegistry* reg, SharedTermId id) {
    if (!reg) return "st" + std::to_string(id);
    auto* st = reg->get(id);
    if (!st) return "st" + std::to_string(id);
    return st->name;
}

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

TheoryCheckResult TheoryManager::check(TheoryLemmaDatabase& lemmaDb, TheoryEffort effort) {
    NO_DBG << "\n========== NO model check #" << (++noDebugModelCheckId) << " ==========\n";

    auto makeFalsifiedConflict = [](const std::vector<SatLit>& rawReasons) {
        TheoryConflict fc;
        fc.clause.reserve(rawReasons.size());
        for (auto lit : rawReasons) {
            fc.clause.push_back(lit.negated());
        }
        return fc;
    };

    if (!combinationMode_) {
        // Legacy single-theory path
        if (solvers_.empty()) {
            NO_DBG << "[NO-RET-0] legacy: no solvers -> Consistent\n";
            return TheoryCheckResult::consistent();
        }
        for (auto& solver : solvers_) {
            auto tr = solver->check(lemmaDb, effort);
            if (tr.kind == TheoryCheckResult::Kind::Conflict && tr.conflictOpt) {
                auto fc = makeFalsifiedConflict(tr.conflictOpt->clause);
                return TheoryCheckResult::mkConflict(std::move(fc));
            }
            if (tr.kind != TheoryCheckResult::Kind::Consistent) {
                NO_DBG << "[NO-RET-1] legacy solver=" << (int)solver->id()
                       << " kind=" << (int)tr.kind << "\n";
                return tr;
            }
        }
        NO_DBG << "[NO-RET-2] legacy: all consistent\n";
        return TheoryCheckResult::consistent();
    }

    // ---- Nelson-Oppen combination path ----

    std::cerr << "[NO] pendingSharedEqEvents=" << pendingSharedEqEvents_.size() << "\n";
    for (auto& ev : pendingSharedEqEvents_) {
        std::cerr << "[NO] pending " << (ev.isEquality ? "EQ " : "NEQ")
               << " " << stName(sharedTermRegistry_, ev.a)
               << " " << stName(sharedTermRegistry_, ev.b)
               << " reason=" << debug::fmtLit(ev.reasonLit)
               << " level=" << ev.decisionLevel << "\n";
    }

    // 1. Process pending SAT-assigned shared equalities/disequalities
    for (auto& ev : pendingSharedEqEvents_) {
        if (ev.isEquality) {
            sharedEqMgr_.assertEquality(ev.a, ev.b, ev.reasonLit);
            if (auto c = sharedEqMgr_.checkDisequalityConflict()) {
                pendingSharedEqEvents_.clear();
                auto fc = makeFalsifiedConflict(c->clause);
                NO_DBG << "[NO-RET-3] SEM conflict after EQ: "
                       << debug::fmtClause(fc.clause) << "\n";
                return TheoryCheckResult::mkConflict(std::move(fc));
            }
            for (auto* solver : solversOwning(ev.a, ev.b)) {
                auto r = solver->assertInterfaceEquality(ev.a, ev.b, ev.reasonLit, ev.decisionLevel);
                if (r.kind == TheoryCheckResult::Kind::Conflict && r.conflictOpt) {
                    r.conflictOpt = makeFalsifiedConflict(r.conflictOpt->clause);
                }
                if (r.kind != TheoryCheckResult::Kind::Consistent) {
                    pendingSharedEqEvents_.clear();
                    NO_DBG << "[NO-RET-4] solver=" << (int)solver->id()
                           << " conflict on IEQ: " << debug::fmtClause(r.conflictOpt->clause) << "\n";
                    return r;
                }
            }
        } else {
            sharedEqMgr_.assertDisequality(ev.a, ev.b, ev.reasonLit);
            if (auto c = sharedEqMgr_.checkDisequalityConflict()) {
                pendingSharedEqEvents_.clear();
                auto fc = makeFalsifiedConflict(c->clause);
                NO_DBG << "[NO-RET-5] SEM conflict after NEQ: "
                       << debug::fmtClause(fc.clause) << "\n";
                return TheoryCheckResult::mkConflict(std::move(fc));
            }
            for (auto* solver : solversOwning(ev.a, ev.b)) {
                std::cerr << "[NO] IDISEQ solver=" << (int)solver->id() << " a=" << ev.a << " b=" << ev.b << "\n";
                auto r = solver->assertInterfaceDisequality(ev.a, ev.b, ev.reasonLit, ev.decisionLevel);
                if (r.kind == TheoryCheckResult::Kind::Conflict && r.conflictOpt) {
                    r.conflictOpt = makeFalsifiedConflict(r.conflictOpt->clause);
                }
                if (r.kind != TheoryCheckResult::Kind::Consistent) {
                    pendingSharedEqEvents_.clear();
                    NO_DBG << "[NO-RET-6] solver=" << (int)solver->id()
                           << " conflict on IDISEQ: " << debug::fmtClause(r.conflictOpt->clause) << "\n";
                    return r;
                }
            }
        }
    }
    pendingSharedEqEvents_.clear();

    // 2. Run each theory check
    for (auto& solver : solvers_) {
        NO_DBG << "[NO] checking solver=" << (int)solver->id() << "\n";
        auto tr = solver->check(lemmaDb, effort);
        if (tr.kind == TheoryCheckResult::Kind::Conflict && tr.conflictOpt) {
            // Defensive: every raw reason should be true in the current model.
            if (assignmentView_) {
                for (auto lit : tr.conflictOpt->clause) {
                    if (assignmentView_->value(lit) != LitValue::True) {
                        std::cerr << "[BUG] Theory conflict contains non-true raw reason: "
                                  << debug::fmtLit(lit) << "\n";
                    }
                }
            }
            tr.conflictOpt = makeFalsifiedConflict(tr.conflictOpt->clause);
        }
        if (tr.kind != TheoryCheckResult::Kind::Consistent) {
            NO_DBG << "[NO-RET-7] solver=" << (int)solver->id()
                   << " kind=" << (int)tr.kind;
            if (tr.conflictOpt) {
                NO_DBG << " clause=" << debug::fmtClause(tr.conflictOpt->clause);
            }
            if (tr.lemmaOpt) {
                NO_DBG << " lemma=" << debug::fmtClause(tr.lemmaOpt->lits);
            }
            NO_DBG << "\n";
            return tr;
        }
    }

    // 3. Collect theory-propagated shared equalities
    for (size_t i = 0; i < solvers_.size(); ++i) {
        auto* solver = solvers_[i].get();
        if (!solver->supportsCombination()) continue;
        auto props = solver->getDeducedSharedEqualities();
        NO_DBG << "[NO] solver=" << (int)solver->id()
               << " deducedEqualities=" << props.size() << "\n";
        for (auto& prop : props) {
            SatLit eqLit = registry_->getOrCreateSharedEqualityAtom(prop.a, prop.b);
            NO_DBG << "[NO] deduced EQ " << stName(sharedTermRegistry_, prop.a)
                   << " = " << stName(sharedTermRegistry_, prop.b)
                   << " atom=" << debug::fmtLit(eqLit) << "\n";
            if (assignmentView_) {
                LitValue val = assignmentView_->value(eqLit);
                if (val == LitValue::True) {
                    NO_DBG << "  already true in model\n";
                    continue;
                }
            }

            ReportedPropKey key{solver->id(), prop.a, prop.b};
            if (deducedEqCache_.count(key)) {
                NO_DBG << "  cached, skip\n";
                continue;
            }
            deducedEqCache_.insert(key);

            TheoryLemma lemma;
            for (auto& reason : prop.reasons) {
                lemma.lits.push_back(reason.negated());
            }
            lemma.lits.push_back(eqLit);
            NO_DBG << "[NO-RET-8] lemma=" << debug::fmtClause(lemma.lits) << "\n";
            if (lemmaDb.insertIfNew(lemma)) {
                return TheoryCheckResult::mkLemma(std::move(lemma));
            }
        }
    }

    NO_DBG << "[NO-RET-9] Consistent\n";
    return TheoryCheckResult::consistent();
}

std::optional<TheorySolver::TheoryModel> TheoryManager::getModel() const {
    TheorySolver::TheoryModel aggregated;
    for (const auto& solver : solvers_) {
        auto m = solver->getModel();
        if (m) {
            for (const auto& [name, value] : m->assignments) {
                aggregated.assignments[name] = value;
            }
        }
    }
    if (aggregated.assignments.empty()) return std::nullopt;
    return aggregated;
}

} // namespace nlcolver
