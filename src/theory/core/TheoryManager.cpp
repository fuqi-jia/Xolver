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
#include <cstdlib>
#include <map>
#include <functional>

namespace zolver {

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
    emittedArrangementSplits_.clear();
    careGraph_.clear();
    aggStats_ = AggregateStats{};
}

void TheoryManager::ensureCareGraph() {
    if (!careGraphEnvChecked_) {
        careGraphEnabled_ = (std::getenv("ZOLVER_COMB_CAREGRAPH") != nullptr);
        careGraphEnvChecked_ = true;
    }
    if (!careGraphEnabled_ || careGraph_.built()) return;
    if (!sharedTermRegistry_) return;
    const CoreIr* ir = sharedTermRegistry_->coreIr();
    if (!ir) return;
    careGraph_.build(*ir, *sharedTermRegistry_);
    // Hand the built care graph to every solver so their O(n^2)
    // getDeducedSharedEqualities loops can prune inert shared-term pairs.
    for (auto& s : solvers_) s->setCareGraph(&careGraph_);
}

bool TheoryManager::useSatMin() {
    if (!satMinEnvChecked_) {
        satMinEnabled_ = (std::getenv("ZOLVER_SAT_MIN") != nullptr);
        satMinEnvChecked_ = true;
    }
    return satMinEnabled_;
}

bool TheoryManager::useModelBased() {
    if (!modelBasedEnvChecked_) {
        modelBasedEnabled_ = (std::getenv("ZOLVER_COMB_MODEL_BASED") != nullptr);
        modelBasedEnvChecked_ = true;
    }
    return modelBasedEnabled_;
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

    bool satMin = useSatMin();
    auto makeFalsifiedConflict = [satMin](const std::vector<SatLit>& rawReasons) {
        TheoryConflict fc;
        fc.clause.reserve(rawReasons.size());
        for (auto lit : rawReasons) {
            fc.clause.push_back(lit.negated());
        }
        // Theory-agnostic minimization (ZOLVER_SAT_MIN): dedup the negated
        // reasons. Sound — dedup preserves the literal set, so falsified-ness
        // is unchanged — and strictly shortens the learned clause.
        if (satMin) ConflictMinimizer::dedup(fc.clause);
        return fc;
    };

    // Soundness guard for interface-(dis)equality conflicts.
    // A conflict over shared-equality atoms is genuine iff the positive
    // equalities entail every negated equality (i.e. for each asserted
    // disequality a!=b in the conflict, a and b are connected by the positive
    // equalities). The EUF explanation occasionally returns a reason set that
    // does not actually entail the merge (incomplete proof-forest explanation),
    // yielding an UNSOUND conflict that excludes valid models -> false UNSAT
    // (e.g. QF_UFLIA hash_sat_03_08). Independently re-verify with a union-find
    // over the conflict's own shared-equality reasons. Conflicts containing any
    // non-shared-equality literal are trusted (theory bounds are sound and not
    // checkable here). Returns true if genuine (or unverifiable), false if the
    // reasons provably do not entail the contradiction.
    auto conflictIsGenuine = [this](const std::vector<SatLit>& rawReasons) -> bool {
        if (!registry_) return true;
        std::map<SharedTermId, SharedTermId> parent;
        std::function<SharedTermId(SharedTermId)> find =
            [&](SharedTermId x) {
                auto it = parent.find(x);
                if (it == parent.end()) { parent[x] = x; return x; }
                if (it->second == x) return x;
                SharedTermId r = find(it->second);
                parent[x] = r;
                return r;
            };
        auto unite = [&](SharedTermId a, SharedTermId b) {
            parent[find(a)] = find(b);
        };
        std::vector<std::pair<SharedTermId, SharedTermId>> negPairs;
        for (auto lit : rawReasons) {
            const auto* rec = registry_->findBySatVar(lit.var);
            if (!rec) return true;  // unknown atom -> trust
            auto* se = std::get_if<SharedEqualityPayload>(&rec->payload);
            if (!se) return true;   // non-shared-eq literal -> trust
            if (lit.sign) unite(se->a, se->b);     // positive: a = b
            else negPairs.push_back({se->a, se->b}); // negative: a != b asserted
        }
        for (auto& [a, b] : negPairs) {
            if (find(a) != find(b)) return false;  // positives do NOT entail a=b
        }
        return true;
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

    // Build the demand-driven care graph once (no-op unless ZOLVER_COMB_CAREGRAPH).
    ensureCareGraph();

    // 1. Process pending SAT-assigned shared equalities/disequalities
    for (auto& ev : pendingSharedEqEvents_) {
        if (ev.isEquality) {
            // Distinct numeric constants are implicitly disequal. An interface
            // equality between two numeric-constant shared terms with different
            // values (e.g. the array Row2 split asserting (1 = 2)) is an
            // immediate contradiction that no arith solver constrains when both
            // sides are constants — getOrCreateInterfaceEqAuxVar returns -1 for
            // const/const pairs. Refute it here so the false disjunct cannot be
            // chosen to satisfy a Row2/Ext lemma. The reason is the equality
            // literal alone: (c1 = c2) is unconditionally false.
            if (sharedTermRegistry_ && ev.a != ev.b) {
                auto va = sharedTermRegistry_->constValue(ev.a);
                auto vb = sharedTermRegistry_->constValue(ev.b);
                if (va && vb && *va != *vb) {
                    pendingSharedEqEvents_.clear();
                    TheoryConflict fc;
                    fc.clause.push_back(ev.reasonLit.negated());
                    NO_DBG << "[NO-RET-CONST] distinct-const IEQ refuted: "
                           << debug::fmtClause(fc.clause) << "\n";
                    return TheoryCheckResult::mkConflict(std::move(fc));
                }
            }
            sharedEqMgr_.assertEquality(ev.a, ev.b, ev.reasonLit);
            if (auto c = sharedEqMgr_.checkDisequalityConflict()) {
                pendingSharedEqEvents_.clear();
                if (!conflictIsGenuine(c->clause))
                    return TheoryCheckResult::unknown("euf: unverifiable interface conflict");
                auto fc = makeFalsifiedConflict(c->clause);
                NO_DBG << "[NO-RET-3] SEM conflict after EQ: "
                       << debug::fmtClause(fc.clause) << "\n";
                return TheoryCheckResult::mkConflict(std::move(fc));
            }
            for (auto* solver : solversOwning(ev.a, ev.b)) {
                auto r = solver->assertInterfaceEquality(ev.a, ev.b, ev.reasonLit, ev.decisionLevel);
                if (r.kind == TheoryCheckResult::Kind::Conflict && r.conflictOpt) {
                    if (!conflictIsGenuine(r.conflictOpt->clause)) {
                        pendingSharedEqEvents_.clear();
                        return TheoryCheckResult::unknown("euf: unverifiable interface conflict");
                    }
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
                if (!conflictIsGenuine(c->clause))
                    return TheoryCheckResult::unknown("euf: unverifiable interface conflict");
                auto fc = makeFalsifiedConflict(c->clause);
                NO_DBG << "[NO-RET-5] SEM conflict after NEQ: "
                       << debug::fmtClause(fc.clause) << "\n";
                return TheoryCheckResult::mkConflict(std::move(fc));
            }
            for (auto* solver : solversOwning(ev.a, ev.b)) {
                auto r = solver->assertInterfaceDisequality(ev.a, ev.b, ev.reasonLit, ev.decisionLevel);
                if (r.kind == TheoryCheckResult::Kind::Conflict && r.conflictOpt) {
                    if (!conflictIsGenuine(r.conflictOpt->clause)) {
                        pendingSharedEqEvents_.clear();
                        return TheoryCheckResult::unknown("euf: unverifiable interface conflict");
                    }
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
            if (!conflictIsGenuine(tr.conflictOpt->clause)) {
                // Spurious interface-(dis)equality conflict: the reasons do not
                // entail the merged equality (incomplete EUF explanation). Never
                // emit a false UNSAT from it — report Unknown (sound).
                return TheoryCheckResult::unknown("euf: unverifiable interface conflict");
            }
            tr.conflictOpt = makeFalsifiedConflict(tr.conflictOpt->clause);
        }
        if (tr.kind != TheoryCheckResult::Kind::Consistent) {
            NO_DBG << "[TM-CHECK] solver=" << (int)solver->id()
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
            // Care-graph prune: a deduced equality between two terms that
            // neither appears in a function/array-arg nor an Eq/Distinct cannot
            // fire any EUF inference, so skip materializing its atom/lemma. Not
            // propagating a sound fact can never create a conflict (no wrong
            // UNSAT); at worst it loses a refinement caught by ModelValidator.
            if (careGraphEnabled_ && !careGraph_.caresPair(prop.a, prop.b)) {
                NO_DBG << "[NO] care-graph skip deduced EQ "
                       << stName(sharedTermRegistry_, prop.a) << " = "
                       << stName(sharedTermRegistry_, prop.b) << "\n";
                continue;
            }
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
            // Minimize (ZOLVER_SAT_MIN) the reason side before appending the
            // implied-equality literal, then re-append: dedup must not drop the
            // (unique) consequent. Sound — the lemma's literal set is preserved.
            if (satMin) ConflictMinimizer::dedup(lemma.lits);
            lemma.lits.push_back(eqLit);
            NO_DBG << "[NO-RET-8] lemma=" << debug::fmtClause(lemma.lits) << "\n";
            if (lemmaDb.insertIfNew(lemma)) {
                return TheoryCheckResult::mkLemma(std::move(lemma));
            }
        }
    }

    // 4. Model-based arrangement splitting.
    //
    // The per-theory models can be each-consistent yet globally inconsistent
    // because the Nelson-Oppen ARRANGEMENT over shared scalars is incomplete:
    // arith freely picks values for unconstrained shared index/element terms
    // (e.g. i0 = i1 = 0), but that implied equality is never decided by SAT, so
    // EUF/the array reasoner never sees it and cannot fire Row1/congruence. The
    // combined point validates per-theory but the combination then returns a
    // globally-inconsistent model:
    //   - array logics: model-validation downgrades Sat -> Unknown;
    //   - QF_UFLIA/UFNIA/UFNRA: a genuinely UNSAT formula (e.g. a UF pigeonhole
    //     over a bounded integer domain) is reported SAT because the arrangement
    //     that would expose the congruence conflict was never closed (the
    //     existing combination false-SAT class).
    //
    // Fix (only at Full effort): when two USER (non-internal) shared scalar
    // terms have the SAME arith-model value but are NOT yet merged in EUF and
    // their interface (dis)equality is still undecided, emit ONE arrangement
    // SPLIT lemma  (a = b) OR (not (a = b))  over the shared-equality atom that
    // both theories observe. The split is a tautology, so it is sound by
    // construction; the SAT solver must commit, and EUF/arith then react through
    // the validated interface (dis)equality paths (EUF refutes a bad merge;
    // arith honors a decided disequality via allowInterfaceDiseqModelBranch).
    // Once every same-value pair is decided, the arrangement is CLOSED and the
    // model read off is globally faithful. Deduped by stable pair key (finite
    // #pairs => terminates).
    //
    // Scope: array combination logics always (arrayCombinationMode_); under
    // ZOLVER_COMB_MODEL_BASED, additionally the LIA-based non-convex combined
    // logic QF_UFLIA. Excluded:
    //   - UFLRA (convex: deduced-equality sharing is already complete);
    //   - UFNIA/UFNRA: their nonlinear solver (NIA/NRA) does not expose
    //     sharedTermArithValue and the arrangement+nonlinear-branch interaction
    //     does not converge (the LIA/LRA mirror's value drives a split that NIA
    //     keeps re-opening -> non-termination). NIA/NRA model extraction is a
    //     separate (A2) workstream; gating it out here keeps this fix sound AND
    //     terminating for the bucket it actually fixes.
    bool hasNonlinearArith = solverByTheory_.count(TheoryId::NIA) ||
                             solverByTheory_.count(TheoryId::NRA) ||
                             solverByTheory_.count(TheoryId::NIRA);
    bool modelArrange = arrayCombinationMode_ ||
                        (useModelBased() && nonConvexMode_ && !hasNonlinearArith);
    if (modelArrange && effort == TheoryEffort::Full &&
        sharedTermRegistry_ && registry_) {
        // Identify the EUF (array) solver to consult for "already merged?".
        TheorySolver* eufSolver = nullptr;
        auto eufIt = solverByTheory_.find(TheoryId::EUF);
        if (eufIt != solverByTheory_.end()) eufSolver = eufIt->second;

        // Collect user (non-internal) shared SCALAR terms together with their
        // current arith-model value (from whichever arith solver owns them).
        struct ValuedTerm { SharedTermId id; SortId sort; RealValue val; };
        std::vector<ValuedTerm> valued;
        for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
            const auto* st = sharedTermRegistry_->get(stId);
            if (!st || st->isInternal) continue;   // scope to user terms only
            // Skip numeric-constant shared terms: a constant-vs-variable
            // arrangement is not needed (the variable's value already coincides
            // with the constant in this model, but they are NOT required equal),
            // and splitting on it destabilizes array axiom instantiation. Only
            // genuine variable-variable arrangements need a split.
            if (sharedTermRegistry_->constValue(stId)) continue;
            std::optional<RealValue> v;
            for (auto& solver : solvers_) {
                if (solver->id() == TheoryId::EUF) continue;
                if (!solver->supportsCombination()) continue;
                v = solver->sharedTermArithValue(stId);
                if (v) break;
            }
            if (!v) continue;
            valued.push_back({stId, st->sort, std::move(*v)});
        }

        for (size_t i = 0; i < valued.size(); ++i) {
            for (size_t j = i + 1; j < valued.size(); ++j) {
                const auto& A = valued[i];
                const auto& B = valued[j];
                if (A.sort != B.sort) continue;         // only same-sort scalars
                if (!(A.val == B.val)) continue;        // arith disagrees -> no split
                // Care-graph prune (demand-driven arrangement): only split a
                // pair some theory cares about (index/element/UF-arg or an
                // Eq/Distinct operand). Skipping an inert pair cannot fire any
                // array axiom, so it is sound (an unsplit globally-inconsistent
                // model is caught by ModelValidator, never wrong UNSAT).
                if (careGraphEnabled_ && !careGraph_.caresPair(A.id, B.id)) continue;
                // Already arranged on the interface? (SAT committed eq/diseq.)
                if (sharedEqMgr_.same(A.id, B.id)) continue;
                if (sharedEqMgr_.diseqKnown(A.id, B.id)) continue;
                // Already merged in EUF (congruence / Row1) -> consistent.
                if (eufSolver && eufSolver->sharedTermsMerged(A.id, B.id)) continue;

                SharedTermId lo = A.id < B.id ? A.id : B.id;
                SharedTermId hi = A.id < B.id ? B.id : A.id;
                uint64_t key = (static_cast<uint64_t>(lo) << 32) |
                               static_cast<uint64_t>(hi);
                if (!emittedArrangementSplits_.insert(key).second) continue;

                // Authorize the owning arith solver(s) to honor (model-branch)
                // a DECIDED interface disequality on this exact pair: this split
                // is the one that may force (a != b), and arith must then keep
                // the convex model from re-equating them. Scoped to this pair so
                // array-reasoner-managed disequalities are unaffected.
                for (auto* owner : solversOwning(A.id, B.id)) {
                    owner->allowInterfaceDiseqModelBranch(A.id, B.id);
                }

                SatLit eqLit = registry_->getOrCreateSharedEqualityAtom(A.id, B.id);
                TheoryLemma lemma;
                lemma.lits.push_back(eqLit);
                lemma.lits.push_back(eqLit.negated());
                NO_DBG << "[NO-ARRANGE] split "
                       << stName(sharedTermRegistry_, A.id) << " = "
                       << stName(sharedTermRegistry_, B.id) << " : "
                       << debug::fmtClause(lemma.lits) << "\n";
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

} // namespace zolver
