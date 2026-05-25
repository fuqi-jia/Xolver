#include "theory/core/TheoryManager.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/DebugTrace.h"
#include "theory/arith/linear/LinearExpr.h"
#include "sat/SatSolver.h"
#include <cassert>
#include <algorithm>
#include <unordered_map>
#include <gmpxx.h>

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
    aggStats_ = AggregateStats{};
}

std::vector<std::string> TheoryManager::activeTheoryNames() const {
    std::vector<std::string> names;
    names.reserve(solvers_.size());
    for (const auto& s : solvers_) {
        switch (s->id()) {
            case TheoryId::LRA: names.push_back("LRA"); break;
            case TheoryId::LIA: names.push_back("LIA"); break;
            case TheoryId::NRA: names.push_back("NRA"); break;
            case TheoryId::NIA: names.push_back("NIA"); break;
            case TheoryId::LIRA: names.push_back("LIRA"); break;
            case TheoryId::NIRA: names.push_back("NIRA"); break;
            case TheoryId::IDL: names.push_back("IDL"); break;
            case TheoryId::RDL: names.push_back("RDL"); break;
            case TheoryId::EUF: names.push_back("EUF"); break;
            case TheoryId::Combination: names.push_back("Combination"); break;
            default: names.push_back("Unknown"); break;
        }
    }
    return names;
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

std::vector<ActiveLinearConstraint> TheoryManager::collectActiveLinearConstraints() const {
    std::vector<ActiveLinearConstraint> result;
    if (!assignmentView_ || !registry_) return result;

    for (const auto& rec : registry_->records()) {
        if (!std::holds_alternative<LinearAtomPayload>(rec.payload)) continue;

        LitValue lv = assignmentView_->value(SatLit{rec.satVar, true});
        if (lv == LitValue::Unknown) continue;
        bool isTrue = (lv == LitValue::True);
        const auto& orig = std::get<LinearAtomPayload>(rec.payload);

        ActiveLinearConstraint alc;
        alc.reasonLit = SatLit{rec.satVar, isTrue};
        alc.payload = orig;
        if (!isTrue) {
            alc.payload.rel = negateRelation(orig.rel);
        }
        result.push_back(alc);
    }
    return result;
}

TheoryCheckResult TheoryManager::check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    NO_DBG << "\n========== NO model check #" << (++noDebugModelCheckId) << " ==========\n";

    auto makeFalsifiedConflict = [](const std::vector<SatLit>& rawReasons) {
        TheoryConflict fc;
        fc.clause.reserve(rawReasons.size());
        for (auto lit : rawReasons) {
            fc.clause.push_back(lit.negated());
        }
        return fc;
    };

    auto recordCheckResult = [this](const TheoryCheckResult& tr) {
        ++aggStats_.checkCalls;
        if (tr.kind == TheoryCheckResult::Kind::Conflict) {
            ++aggStats_.conflicts;
            if (tr.conflictOpt && !tr.conflictOpt->clause.empty()) {
                size_t sz = tr.conflictOpt->clause.size();
                aggStats_.totalConflictSize += static_cast<int64_t>(sz);
                if (static_cast<int64_t>(sz) > aggStats_.maxConflictSize)
                    aggStats_.maxConflictSize = static_cast<int64_t>(sz);
            }
        } else if (tr.kind == TheoryCheckResult::Kind::Lemma) {
            ++aggStats_.lemmas;
        }
    };

    if (!combinationMode_) {
        // Legacy single-theory path
        if (solvers_.empty()) {
            return TheoryCheckResult::consistent();
        }
        auto activeLinearContext = collectActiveLinearConstraints();
        for (auto& solver : solvers_) {
            solver->setActiveLinearContext(&activeLinearContext);
            auto tr = solver->check(lemmaDb, effort);
            recordCheckResult(tr);
            if (tr.kind == TheoryCheckResult::Kind::Conflict && tr.conflictOpt) {
                auto fc = makeFalsifiedConflict(tr.conflictOpt->clause);
                return TheoryCheckResult::mkConflict(std::move(fc));
            }
            if (tr.kind != TheoryCheckResult::Kind::Consistent) {
                return tr;
            }
        }
        return TheoryCheckResult::consistent();
    }

    // ---- Nelson-Oppen combination path ----

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
        auto tr = solver->check(lemmaDb, effort);
        recordCheckResult(tr);
        if (tr.kind == TheoryCheckResult::Kind::Conflict && tr.conflictOpt) {
            std::cerr << "[TM-CONFLICT] solver=" << (int)solver->id() << " clause=";
            for (auto lit : tr.conflictOpt->clause) {
                std::cerr << debug::fmtLit(lit) << " ";
            }
            std::cerr << "\n";
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
            std::cerr << "[TM-CHECK] solver=" << (int)solver->id()
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
    // First-registered solver wins per variable. Solvers are registered with
    // the PRIMARY theory first (e.g. NIA before the LIA-linearization helper
    // for QF_NIA), so the authoritative theory's validated witness is kept
    // and helper solvers (whose models are linear-only / incomplete and can
    // violate nonlinear constraints) only fill in variables the primary did
    // not assign. Without this, the LIA mirror's linear-feasible point
    // overrode NIA's witness, producing models that satisfy the linear part
    // but not the nonlinear constraints (e.g. nia_089: sum=20 ok, product<100).
    TheorySolver::TheoryModel aggregated;
    // For array-combination logics (QF_ALIA/ALRA/AUFLIA/AUFLRA) the array
    // theory (EUF) and the arithmetic theory each model the index/element
    // scalars differently: EUF assigns opaque equality tokens ("@e..."), arith
    // assigns concrete numbers. EUF's array interps reference those tokens, but
    // the index/element scalar's TRUE value (subject to arith bounds like
    // i > 1) lives in the arith model. We must reconcile: a token's numeric
    // value is the arith value of any scalar EUF placed in that token's class.
    // Collect the arith numeric assignments separately so we can rewrite the
    // EUF tokens to those numbers before aggregating. Without this, dumping an
    // EUF opaque token as a freshly-minted number can violate an arith bound
    // (unsound printed model) while the validator sees Indeterminate and lets
    // it through.
    std::unordered_map<std::string, std::string> arithNum;  // var -> numeric str
    for (const auto& solver : solvers_) {
        auto m = solver->getModel();
        if (!m) continue;
        if (solver->id() == TheoryId::EUF) continue;  // tokens, not numbers
        for (const auto& [name, value] : m->assignments) {
            if (value == "true" || value == "false") continue;
            if (value.empty() || value[0] == '@') continue;  // not a number
            arithNum.emplace(name, value);  // first arith wins
        }
    }

    for (const auto& solver : solvers_) {
        auto m = solver->getModel();
        if (m) {
            for (const auto& [name, value] : m->assignments) {
                aggregated.assignments.insert({name, value});  // first wins
            }
            for (const auto& [name, value] : m->numericAssignments) {
                aggregated.numericAssignments.insert({name, value});  // first wins
            }
            for (const auto& [name, interp] : m->functionInterps) {
                aggregated.functionInterps.insert({name, interp});  // first wins
            }
            for (const auto& [name, interp] : m->arrayInterps) {
                aggregated.arrayInterps.insert({name, interp});  // first wins
            }
        }
    }

    // Build token -> "#n:<rational>" using each scalar that has BOTH an EUF
    // token and an arith numeric value. (Numeric tokens "#n:.." already carry
    // their value and need no remap.)
    std::unordered_map<std::string, std::string> tokenToNum;
    for (const auto& [name, tok] : aggregated.assignments) {
        if (tok.empty() || tok[0] != '@') continue;     // only opaque tokens
        auto it = arithNum.find(name);
        if (it == arithNum.end()) continue;
        std::string canon;
        try { canon = "#n:" + mpq_class(it->second).get_str(); } catch (...) { continue; }
        // If a token already maps to a DIFFERENT number, the model is
        // internally inconsistent (two arith values in one EUF class). Leave
        // it opaque so the validator/gate can catch the violation rather than
        // silently picking one — soundness over a guessed model.
        auto e = tokenToNum.find(tok);
        if (e != tokenToNum.end()) { if (e->second != canon) e->second = "@CONFLICT"; }
        else tokenToNum.emplace(tok, canon);
    }

    // Preserve EUF DISTINCTNESS: distinct tokens are distinct array indices /
    // elements (an asserted/extensionality-witnessed disequality). If two
    // distinct tokens would map to the SAME arith number, that number is a
    // spurious default (the arith theory left those vars unconstrained and
    // happened to pick the same value) — remapping would collapse i != j into
    // i = j and produce an unsound printed model. Drop the remap for any
    // number claimed by >1 distinct token; those tokens stay opaque and
    // dumpModel mints distinct concrete values for them. (A constrained var
    // with a unique arith value still remaps, e.g. i > 1 -> i = 2.)
    {
        std::unordered_map<std::string, int> numCount;
        for (const auto& [tok, num] : tokenToNum)
            if (num != "@CONFLICT") ++numCount[num];
        for (auto& [tok, num] : tokenToNum)
            if (num != "@CONFLICT" && numCount[num] > 1) num = "@CONFLICT";
    }

    auto remap = [&](std::string& v) {
        auto it = tokenToNum.find(v);
        if (it != tokenToNum.end() && it->second != "@CONFLICT") v = it->second;
    };

    // Rewrite scalar assignments and array interp index/element tokens.
    for (auto& [name, val] : aggregated.assignments) remap(val);
    for (auto& [name, ai] : aggregated.arrayInterps) {
        remap(ai.defaultVal);
        for (auto& [idx, elem] : ai.entries) { remap(idx); remap(elem); }
    }

    if (aggregated.assignments.empty() && aggregated.numericAssignments.empty() &&
        aggregated.functionInterps.empty() && aggregated.arrayInterps.empty())
        return std::nullopt;
    return aggregated;
}

} // namespace nlcolver
