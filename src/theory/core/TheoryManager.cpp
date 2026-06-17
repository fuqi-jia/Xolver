#include "theory/core/TheoryManager.h"
#include "util/EnvParam.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/DebugTrace.h"
#include "theory/arith/linear/LinearExpr.h"
#include "sat/SatSolver.h"
#include "expr/ir.h"
#include <cassert>
#include <algorithm>
#include <unordered_map>
#include <gmpxx.h>
#include <cstdlib>
#include <cctype>
#include <map>
#include <functional>

namespace xolver {

static int noDebugModelCheckId = 0;

// --- XOLVER_COMB_DIAG: per-channel combination-loop emission counters --------
// File-based (worker-thread stderr is suppressed). Confirms which channel
// (arrangement split vs deduced-eq lemma) drives the cs_* matching loop.
extern long g_sharedEqAtomsCreated;   // defined in TheoryAtomRegistry.cpp (xolver scope)
namespace {
struct CombDiag {
    long checks = 0;
    long arrSplitValue = 0, arrSplitDemand = 0, arrSplitUfarg = 0;
    long dedEqLemma = 0, dedEqEufMerged = 0, dedEqAtomFresh = 0;
    long l5IdxTerms = 0, l5PairsQueried = 0, l5Proven = 0;   // FIX-c funnel: arith->array diseq
    long lastDumpCheck = 0;
};
static CombDiag g_cd;
static const bool g_combDiag = xolver::env::diag("XOLVER_COMB_DIAG");
// ⚠️ UNSOUND-WHEN-ON, DEFAULT-OFF, DO-NOT-PROMOTE. Research toggle for the
// combination-loop convergence work (see check()). Skipping the deduced-eq
// publish for EUF-already-merged pairs DOES converge the 444-round loop, but
// the reg UF-bearing gate proved it produces WRONG-SAT on 8 UNSAT cases
// (ufdtnia_002/003/007, uflia_003/006/010, uflra_002, ufdtnia_projection:
// unsat->sat) because the shared-eq atom is the INTER-THEORY conflict channel,
// not redundant. Kept only so the convergence mechanism + its soundness
// boundary are reproducible; the real fix is theory PROPAGATION (keep the eqs,
// propagate forced atoms via cb_propagate). NEVER enable in a shipped binary.
static const bool g_skipEufMergedUNSAFE =
    xolver::env::diag("XOLVER_COMB_SKIP_EUF_MERGED_UNSAFE");
static void combDiagDump() {
    if (!g_combDiag) return;
    if (g_cd.checks - g_cd.lastDumpCheck < 100) return;
    g_cd.lastDumpCheck = g_cd.checks;
    char buf[512];
    int n = std::snprintf(buf, sizeof(buf),
        "checks=%ld\n"
        "arrSplit value=%ld demand=%ld ufarg=%ld (total=%ld)\n"
        "dedEqLemma=%ld dedEqEufMerged(skipped)=%ld dedEqAtomFresh=%ld\n"
        "L5 idxTerms=%ld pairsQueried=%ld proven=%ld\n"
        "sharedEqAtomsCreated(global)=%ld\n",
        g_cd.checks,
        g_cd.arrSplitValue, g_cd.arrSplitDemand, g_cd.arrSplitUfarg,
        g_cd.arrSplitValue + g_cd.arrSplitDemand + g_cd.arrSplitUfarg,
        g_cd.dedEqLemma, g_cd.dedEqEufMerged, g_cd.dedEqAtomFresh,
        g_cd.l5IdxTerms, g_cd.l5PairsQueried, g_cd.l5Proven,
        g_sharedEqAtomsCreated);
    // atomic-ish: write to temp then rename (avoids empty file if killed mid-write)
    FILE* f = std::fopen("/tmp/xolver_combdiag.tmp", "w");
    if (!f) return;
    std::fwrite(buf, 1, n > 0 ? (size_t)n : 0, f);
    std::fclose(f);
    std::rename("/tmp/xolver_combdiag.tmp", "/tmp/xolver_combdiag.txt");
}
}  // namespace

static std::string stName(const SharedTermRegistry* reg, SharedTermId id) {
    if (!reg) return "st" + std::to_string(id);
    auto* st = reg->get(id);
    if (!st) return "st" + std::to_string(id);
    return st->name;
}

void TheoryManager::setArrayCombinationMode(bool v) {
    arrayCombinationMode_ = v;
    // Nelson-Oppen default arrangement: for array-combination logics, default
    // every fresh interface (shared-equality) atom to DISEQUAL so the SAT core
    // stops freely guessing equalities (the cs_* matching loop). Phase-only =
    // sound. Ablation escape: XOLVER_COMB_EQ_DISEQ_PHASE=0.
    if (v && registry_) {
        static const bool diseqPhase = [] {
            const char* e = std::getenv("XOLVER_COMB_EQ_DISEQ_PHASE");
            return !e || !(e[0] == '0' && e[1] == '\0');   // default ON
        }();
        registry_->setDefaultSharedEqDisequal(diseqPhase);
    }
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
    noPropEntailments_.clear();
    emittedArrangementSplits_.clear();
    careGraph_.clear();
    aggStats_ = AggregateStats{};
}

void TheoryManager::ensureCareGraph() {
    if (!careGraphEnvChecked_) {
        // XOLVER_COMB_CAREGRAPH historical default-OFF (env-set toggles ON).
        // Auto-enable under arrayCombinationMode_: QF_ANIA / QF_AUFNIA need the
        // care-graph as the structural bound for the demand-driven arrangement
        // (Phase 2 below). The graph build is cheap (one syntactic scan), the
        // prune is sound (under-approximation per CareGraph.h header), and no
        // existing case regresses (the value-based arrangement still uses the
        // same caresPair filter it did before).
        careGraphEnabled_ = (xolver::env::diag("XOLVER_COMB_CAREGRAPH")) ||
                            arrayCombinationMode_;
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
        satMinEnabled_ = (xolver::env::diag("XOLVER_SAT_MIN"));
        satMinEnvChecked_ = true;
    }
    return satMinEnabled_;
}

bool TheoryManager::useModelBased() {
    if (!modelBasedEnvChecked_) {
        // 2026-06-02 PROMOTE default-ON: closes the residual Wisa false-SAT
        // class (xs-05-16) where arith bridges b_v1 and 0_const have equal
        // model values but EUF doesn't merge them, leaving each x_count call
        // with its own independent arith bridge value, so the arith constraint
        // arg1 = arg0 + 4*x_count(...) + 4*s_count(...) appears satisfied at
        // the SAT layer with mismatched bridge values. The model-based scalar
        // arrangement (at Full effort, lines 631+) emits a SPLIT lemma over
        // every same-arith-value user scalar pair that isn't yet merged in
        // EUF, forcing SAT to commit so EUF can react. Verified default-on:
        //   Wisa(30) FLOOR OFF + COMB_MODEL_BASED=1: 0 unsound
        //   unit 1098/1098, reg 670/670
        // Escape: XOLVER_COMB_MODEL_BASED=0.
        const char* e = std::getenv("XOLVER_COMB_MODEL_BASED");
        modelBasedEnabled_ = e ? !(e[0] == '0' && e[1] == '\0') : true;
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

    // Clear the deduced-equality emission cache on EVERY backtrack:
    // the cache key (solver, a, b) is coarse — it blocks ANY re-emission of
    // the same shared-term pair from the same solver, even when the EUF
    // explanation chain re-establishes a=b under a different SAT branch with
    // a different reason-set (a NOVEL lemma). lemmaDb.insertIfNew is the
    // fine-grained dedup layer (by literal set) and still rejects truly
    // identical lemmas, so dropping the coarse cache on backtrack cannot
    // cause floods — it only restores re-emission of a fact whose reasons
    // changed across the conflict. This is the Wisa-class fix: on branch A,
    // OR-clause picks (= sf(X) adr_lo) and reasons R_A entail bridge_K~bridge_J;
    // backtrack past R_A; on branch B, OR-clause picks (= sf(X) adr_hi) and
    // a different reason-set R_B re-establishes the SAME merge, producing
    // a novel lemma that was previously suppressed by the coarse cache.
    deducedEqCache_.clear();
}

std::vector<ActiveLinearConstraint> TheoryManager::collectActiveLinearConstraints() const {
    std::vector<ActiveLinearConstraint> result;
    if (!assignmentView_ || !registry_) return result;
    result.reserve(activeLinearCountHint_);   // active set is stable across checks ⇒ avoid push_back reallocations

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
    activeLinearCountHint_ = result.size();
    return result;
}

std::vector<TheoryLemma> TheoryManager::takeEntailmentPropagations() {
    // Single-theory: always drain entailments (per-solver Farkas/value-pin
    // propagations are sound by construction).
    //
    // Combination: drain LINEAR-theory entailments (LIA/LRA) even when a
    // nonlinear solver (NIA/NRA/NIRA) is present — the linear sibling is ALWAYS
    // registered alongside the nonlinear one for NIA/NRA/NIRA logics
    // (TheoryFactory::setupSolvers), and LIA/LRA's entailment is sound and
    // well-defined regardless of nonlinear's presence. This is the chain UFLIA/
    // UFLRA/UFNIA/UFNRA all need to close the goal-atom propagation (Wisa class
    // of false-SAT). Nonlinear solvers themselves do not yet implement
    // entailment so the suppression only matters for them.
    std::vector<TheoryLemma> out;
    for (auto& s : solvers_) {
        // Only LIA / LRA contribute entailments today; NIA / NRA / NIRA / EUF
        // override the base no-op. The check below documents intent: it is
        // safe to drain ANY solver's entailments because the base returns {}.
        if (combinationMode_) {
            TheoryId id = s->id();
            bool isLinearArith =
                (id == TheoryId::LIA || id == TheoryId::LRA ||
                 id == TheoryId::IDL || id == TheoryId::RDL);
            // XOLVER_NIA_LINEAR_PROP (default-OFF): also drain NIA's fixed-value
            // entailments in combination. NIA returns {} unless the flag is set, so
            // this is a no-op by default; the producer is sound by construction
            // (global tautology clauses over the real asserted reasons).
            static const bool niaProp = [] {
                return xolver::env::flag("XOLVER_NIA_LINEAR_PROP");
            }();
            // XOLVER_EUF_PROP_COMB (default-OFF, EXPERIMENTAL): drain EUF's
            // entailment propagations in combination (congruence-derived
            // equalities + disequalities over EUF Eq atoms). Each EUF lemma is
            // (¬reasons ∨ implied), an EUF tautology; this forces the congruence
            // consequences instead of leaving them for the SAT core to GUESS (the
            // cs_* matching loop). eqAtomRegistry_ is wired in array logics
            // (EufSolver::enableArrays) so EUF actually emits.
            // ★ SOUNDNESS RISK: an EUF explanation can rest on a STALE interface-eq
            // merge -> invalid reason clause -> wrong-UNSAT (xs_11_11/xs_15_15
            // class). The L9 firewall guards this, but the flag stays default-OFF
            // and is NOT promoted until full regression is 0-unsound.
            static const bool eufPropComb = [] {
                return xolver::env::flag("XOLVER_EUF_PROP_COMB");
            }();
            bool allow = isLinearArith || (id == TheoryId::NIA && niaProp) ||
                         (id == TheoryId::EUF && eufPropComb);
            if (!allow) continue;
        }
        auto v = s->takeEntailmentPropagations();
        // Diagnostic emission counter (fd-2, periodic) for the cs_* probe: how many
        // entailment lemmas each theory actually emits in combination. Env-gated,
        // default-inert.
        static const bool entDiag = xolver::env::diag("XOLVER_ENTAIL_DIAG");
        if (entDiag && !v.empty()) {
            std::fprintf(stderr, "[ENTAIL] theory=%d emitted=%zu\n",
                         static_cast<int>(s->id()), v.size());
            std::fflush(stderr);
        }
        for (auto& l : v) out.push_back(std::move(l));
    }
    // L4-reach: drain TheoryManager-level entailments (array-relevant deduced
    // shared eqs routed to Standard under XOLVER_NIA_NO_PROP). Empty by default.
    for (auto& l : noPropEntailments_) out.push_back(std::move(l));
    noPropEntailments_.clear();

    // L13: drain relevancy-bounded Row2 case-split lemmas (XOLVER_AX_ROW2_SPLIT).
    // Each is an array-axiom TAUTOLOGY (i=j ∨ readEq), tagged ArraySplit so the
    // propagator can mark its atoms dynamically relevant. Unconditionally sound to
    // add regardless of mode — no combination gating.
    // Default-ON: completeness tautology, not a heuristic (=0 is a kill-switch).
    static const bool row2Split = [] {
        return xolver::env::flag("XOLVER_AX_ROW2_SPLIT", true);
    }();
    // Scoped to COMBINATION mode: pure QF_AX has its own complete Full-effort
    // array sat-gate that Standard-effort splits perturb (ax_007 unsat→unknown);
    // the integrated split only targets combination array+arith (cs_* / QF_ANIA).
    if (row2Split && combinationMode_) {
        for (auto& s : solvers_) {
            auto splits = s->takeArraySplitLemmas();
            for (auto& l : splits) out.push_back(std::move(l));
        }
    } else if (row2Split) {
        // Drain + discard so the buffer doesn't accumulate in single-theory mode.
        for (auto& s : solvers_) (void)s->takeArraySplitLemmas();
    }
    return out;
}

std::optional<bool> TheoryManager::evalTheoryAtom(SatVar v) {
    if (!registry_) return std::nullopt;
    const TheoryAtomRecord* rec = registry_->findBySatVar(v);
    if (!rec) return std::nullopt;
    auto it = solverByTheory_.find(rec->theory);
    if (it == solverByTheory_.end()) return std::nullopt;
    return it->second->evalAtomAtModel(v);
}

TheoryCheckResult TheoryManager::check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    NO_DBG << "\n========== NO model check #" << (++noDebugModelCheckId) << " ==========\n";
    if (g_combDiag) { ++g_cd.checks; combDiagDump(); }

    bool satMin = useSatMin();
    auto makeFalsifiedConflict = [satMin](const std::vector<SatLit>& rawReasons) {
        TheoryConflict fc;
        fc.clause.reserve(rawReasons.size());
        for (auto lit : rawReasons) {
            fc.clause.push_back(lit.negated());
        }
        // Theory-agnostic minimization (XOLVER_SAT_MIN): dedup the negated
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

    // Build the demand-driven care graph once (no-op unless XOLVER_COMB_CAREGRAPH).
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
                    // Capture the reason literal BEFORE clear(): clear() destroys
                    // the vector elements, after which `ev` dangles. Reading
                    // ev.reasonLit post-clear was a use-after-free that put a
                    // freed-memory (garbage, unregistered) literal into the
                    // conflict -> a 1-lit {¬garbage} clause the propagator could
                    // not falsify -> ABORT-388 -> Unknown (cs_* QF_ANIA).
                    SatLit rl = ev.reasonLit;
                    pendingSharedEqEvents_.clear();
                    TheoryConflict fc;
                    fc.clause.push_back(rl.negated());
                    NO_DBG << "[NO-RET-CONST] distinct-const IEQ refuted: "
                           << debug::fmtClause(fc.clause) << "\n";
                    return TheoryCheckResult::mkConflict(std::move(fc));
                }
            }
            sharedEqMgr_.assertEquality(ev.a, ev.b, ev.reasonLit);
            if (xolver::env::diag("XOLVER_L4R_DIAG")) {
                static size_t g_ieq = 0; ++g_ieq;
                if (g_ieq % 50 == 0)
                    std::fprintf(stderr, "[L4R-IEQ] interface-eq merges=%zu\n", g_ieq);
            }
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
    //
    // Iter#28+29: XOLVER_COMB_PUBLISH_ON_LEMMA. When a solver returns Lemma
    // (NOT Conflict / NOT Unknown), save the Lemma but continue to step 3
    // (shared-eq publish + arrangement) before returning. Iter#25-27 pinned
    // the QF_ANIA starvation here: NIA emits ~138 Lemmas per second at
    // Standard effort, and the original short-circuit `return tr` on any
    // non-Consistent skipped step 3 every time — the combination layer's
    // getDeducedSharedEqualities + sharedTermArithValue queries never fired.
    // Publishing on Lemma lets the SAT layer receive BOTH the Lemma
    // (case-split) AND the deduced shared eqs (propagation) in the same
    // cb_propagate round.
    //
    // SOUND: deduced shared eqs are derived from the current trail's bounds
    // and never become weaker when the solver later branches; the Lemma is
    // still returned so SAT honors the case-split. Conflict / Unknown still
    // return immediately (Conflict is UNSAT-direction; Unknown must propagate
    // upstream without spending more time).
    //
    // Iter#29: auto-ON in array-combination mode (arrayCombinationMode_,
    // set by TheoryFactory for QF_ANIA / QF_AUFNIA / QF_AUFLIA / QF_ALIA).
    // Iter#28 verified 0 reg regression on all 16 buckets with flag ON.
    // Iter#32: extended auto-ON to ALL combinationMode_ logics (QF_UFNIA,
    // QF_UFLIA, QF_UFLRA, QF_UFNRA, QF_UFLIRA in addition to the array
    // logics). Iter#28's 16-bucket regression-clean evidence covered the
    // wider scope already; this widens the scope to match. Pure
    // single-theory solving (LIA / LRA / NIA / NRA alone, no combination)
    // retains the previous short-circuit behavior — combinationMode_ is
    // false there, so the starvation pattern doesn't apply. Env override
    // XOLVER_COMB_PUBLISH_ON_LEMMA=1 forces ON (e.g. force-on for an
    // experimental non-combination logic), =0 forces OFF (escape hatch
    // for autotuner or regression bisects).
    bool publishOnLemma = combinationMode_;
    if (const char* e = std::getenv("XOLVER_COMB_PUBLISH_ON_LEMMA")) {
        publishOnLemma = !(e[0] == '0' && e[1] == '\0');
    }
    TheoryCheckResult pendingLemma = TheoryCheckResult::consistent();
    bool havePendingLemma = false;
    static const bool tmHb = xolver::env::diag("XOLVER_TMCHECK_HB");
    for (auto& solver : solvers_) {
        if (tmHb) {
            if (FILE* f = std::fopen("/tmp/xolver_tmcheck.txt", "w")) {
                std::fprintf(f, "phase2 solver=%d effort=%s ENTER\n",
                             (int)solver->id(),
                             effort == TheoryEffort::Full ? "Full" : "Standard");
                std::fclose(f);
            }
        }
        auto tr = solver->check(lemmaDb, effort);
        if (tmHb) {
            if (FILE* f = std::fopen("/tmp/xolver_tmcheck.txt", "w")) {
                std::fprintf(f, "phase2 solver=%d EXIT kind=%d\n",
                             (int)solver->id(), (int)tr.kind);
                std::fclose(f);
            }
        }
        recordCheckResult(tr);
        // Conflict-source attribution (XOLVER_COMB_CONFLICT_TRACE): name the
        // solver behind a combination-path conflict so we can route the eventual
        // correctness fix (e.g. an unsound Standard-effort NIA conflict -> A2).
        if (tr.kind != TheoryCheckResult::Kind::Consistent &&
            std::getenv("XOLVER_COMB_CONFLICT_TRACE")) {
            std::cerr << "[CONFLICT-SRC] solver=" << (int)solver->id()
                      << " effort=" << (effort == TheoryEffort::Full ? "Full" : "Standard")
                      << " kind=" << (int)tr.kind
                      << " size=" << (tr.conflictOpt ? tr.conflictOpt->clause.size() : 0)
                      << "\n";
        }
        if (tr.kind == TheoryCheckResult::Kind::Conflict && tr.conflictOpt) {
            if (!conflictIsGenuine(tr.conflictOpt->clause)) {
                // Spurious interface-(dis)equality conflict: the reasons do not
                // entail the merged equality (incomplete EUF explanation). Never
                // emit a false UNSAT from it — report Unknown (sound).
                return TheoryCheckResult::unknown("euf: unverifiable interface conflict");
            }
            tr.conflictOpt = makeFalsifiedConflict(tr.conflictOpt->clause);
        }
        if (publishOnLemma && tr.kind == TheoryCheckResult::Kind::Lemma) {
            // Save the Lemma + continue to step 3 (publish shared-eqs) before
            // returning. Subsequent solvers' checks are skipped — we don't
            // want to ask them when the SAT layer is about to branch anyway.
            NO_DBG << "[TM-CHECK-LEMMA-DEFER] solver=" << (int)solver->id()
                   << " lemma=" << debug::fmtClause(tr.lemmaOpt->lits) << "\n";
            pendingLemma = std::move(tr);
            havePendingLemma = true;
            break;
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

    // 3. Collect theory-propagated shared equalities.
    // ARRAY-INDEX scoping (read2 fix): an array-index pair's deduced equality
    // (e.g. a computed store index = a read index) must reach the array's pending
    // Row1/Row2. But an early-derivable deduced equality generated at STANDARD
    // effort is dropped by cb_propagate AND cached (deducedEqCache_ + lemmaDb dedup),
    // which permanently blocks its re-emission at FULL effort where propagation is
    // sound. So DEFER array-index-pair deduced equalities to Full effort only — we
    // skip them at Standard so they are neither cached nor lemmaDb-recorded, then
    // emit cleanly at Full. Scoped to array-index pairs (which are few): propagating
    // EVERY deduced equality at Full instead floods the SAT core (broad regressions
    // + a new false-SAT, observed on the blanket attempt). Non-array pairs keep
    // their exact existing behavior (no UFLIA/UFNIA change).
    std::unordered_set<SharedTermId> arrayIdxSet;
    for (auto& s : solvers_) {
        auto v = s->arrayIndexSharedTerms();
        arrayIdxSet.insert(v.begin(), v.end());
        // Value/element side too: a value-pair deduced equality (e.g. two stored
        // values tied equal by a read-over-write chain) hits the same Standard-
        // effort cache-poisoning that the index deferral fixes, so it must also
        // be deferred to Full. Scoped to array value/element terms (not all
        // shared scalars) to avoid the UFLIA/UFNIA flood. (alra_010 value side.)
        auto vv = s->arrayValueSharedTerms();
        arrayIdxSet.insert(vv.begin(), vv.end());
    }

    // ---- L5: demand-driven disequality propagation (XOLVER_NIA_NO_DISEQ) ----
    // BMC memory reasoning is dominated by Row2 (the DISEQUAL-index read-over-
    // write: i!=j => select(store(a,i,v),j) = select(a,j)). The equality
    // connector (L4-reach) alone merges indices but never fires Row2. Here, for
    // each array-index pair, ask each combination solver whether their domains
    // are provably disjoint; route a YES as (¬reasons ∨ ¬eqLit) so CaDiCaL
    // assigns the shared-eq atom FALSE. The propagator then records an EUF
    // disequality, and the existing L2 Row2-cond path fires with the single eqLit
    // reason (the multi-literal domain reason lives in the routed SAT clause — no
    // change to the EUF explanation). Demand-driven + array-pair scoped: bounded
    // by the (small) index set, never O(n^2) over all shared terms. SOUND:
    // proveSharedDisjoint returns a COMPLETE reason (reasons ⟹ a!=b);
    // propagating a disequality the theory already entails cannot create a wrong
    // UNSAT that the disequality alone does not already justify.
    static const bool noDiseq = [] {
        return xolver::env::flag("XOLVER_NIA_NO_DISEQ");
    }();
    if (noDiseq && effort != TheoryEffort::Full && registry_ &&
        arrayIdxSet.size() >= 2) {
        std::vector<SharedTermId> idxv(arrayIdxSet.begin(), arrayIdxSet.end());
        std::sort(idxv.begin(), idxv.end());   // deterministic emission order
        size_t buffered = 0;
        if (g_combDiag) g_cd.l5IdxTerms = (long)idxv.size();
        for (size_t i = 0; i < idxv.size(); ++i) {
            for (size_t j = i + 1; j < idxv.size(); ++j) {
                SharedTermId A = idxv[i], B = idxv[j];
                if (sharedEqMgr_.same(A, B) || sharedEqMgr_.diseqKnown(A, B))
                    continue;
                if (careGraphEnabled_ && !careGraph_.caresPair(A, B)) continue;
                if (g_combDiag) ++g_cd.l5PairsQueried;
                for (auto& s : solvers_) {
                    if (!s->supportsCombination()) continue;
                    auto r = s->proveSharedDisjoint(A, B);
                    if (!r) continue;
                    if (g_combDiag) ++g_cd.l5Proven;
                    SatLit eqLit = registry_->getOrCreateSharedEqualityAtom(A, B);
                    if (assignmentView_ &&
                        assignmentView_->value(eqLit) == LitValue::False) break;
                    TheoryLemma lemma;
                    for (auto& lit : *r) lemma.lits.push_back(lit.negated());
                    if (satMin) ConflictMinimizer::dedup(lemma.lits);
                    lemma.lits.push_back(eqLit.negated());  // ¬(a=b) = a!=b
                    if (lemmaDb.insertIfNew(lemma)) {
                        noPropEntailments_.push_back(std::move(lemma));
                        ++buffered;
                    }
                    break;   // one solver's proof suffices
                }
            }
        }
        static const bool l4rDiag = xolver::env::diag("XOLVER_L4R_DIAG");
        if (l4rDiag && buffered) {
            std::fprintf(stderr, "[L5-DISEQ] buffered=%zu idxTerms=%zu\n",
                         buffered, idxv.size());
            std::fflush(stderr);
        }
    }

    // L11 demand-driven disequality (XOLVER_NIA_ROW2_DEMAND, default-OFF). The
    // blind L5 sweep above queries proveSharedDisjoint over arrayIdxSet (O(idx²),
    // care-graph pruned) — but the index pairs the array reasoner ACTUALLY needs to
    // fire a read-over-write (Row2-cond eligible=N, merges=0 on cs_*) are not
    // necessarily in arrayIdxSet / survive the prune, so their i≠j is never proven
    // and the chain stalls. Here the array reasoner SURFACES exactly those demanded
    // pairs (via takeRow2DemandPairs); we drive proveSharedDisjoint on each and
    // force ¬eqLit through the SAME sound channel (¬reasons ∨ ¬eqLit) the blind
    // sweep uses. Demand-driven => bounded by the reads on the conflict path, not
    // O(idx²). SOUND: identical reason contract (proveSharedDisjoint returns a
    // COMPLETE reason ⟹ a≠b); surfacing a demand cannot create an unsound diseq.
    static const bool row2Demand = [] {
        return xolver::env::flag("XOLVER_NIA_ROW2_DEMAND");
    }();
    if (row2Demand && effort != TheoryEffort::Full && registry_) {
        size_t dBuffered = 0, dQueried = 0;
        for (auto& s : solvers_) {
            if (!s->supportsCombination()) continue;
            auto demand = s->takeRow2DemandPairs();
            for (auto& [A, B] : demand) {
                if (sharedEqMgr_.same(A, B) || sharedEqMgr_.diseqKnown(A, B)) continue;
                ++dQueried;
                // Constant–constant: two DISTINCT numeric-constant index terms are
                // unconditionally disequal — force ¬eqLit with an EMPTY reason
                // (the clause is the unit theorem [¬(A=B)]). This covers the BMC
                // distinct-address reads the Row2-cond path needs but that
                // proveSharedDisjoint refuses (constant pins carry no SAT-literal
                // reason -> its non-empty-reason guard returns null). SOUND: A,B are
                // syntactically distinct constants, so A≠B holds unconditionally.
                if (sharedTermRegistry_) {
                    auto va = sharedTermRegistry_->constValue(A);
                    auto vb = sharedTermRegistry_->constValue(B);
                    if (va && vb) {
                        if (*va == *vb) continue;   // equal constants — not disequal
                        SatLit eqLit = registry_->getOrCreateSharedEqualityAtom(A, B);
                        if (assignmentView_ &&
                            assignmentView_->value(eqLit) == LitValue::False) continue;
                        TheoryLemma lemma;
                        lemma.lits.push_back(eqLit.negated());   // unconditional A≠B
                        if (lemmaDb.insertIfNew(lemma)) {
                            noPropEntailments_.push_back(std::move(lemma));
                            ++dBuffered;
                        }
                        continue;
                    }
                }
                for (auto& s2 : solvers_) {
                    if (!s2->supportsCombination()) continue;
                    auto r = s2->proveSharedDisjoint(A, B);
                    if (!r) continue;
                    SatLit eqLit = registry_->getOrCreateSharedEqualityAtom(A, B);
                    if (assignmentView_ &&
                        assignmentView_->value(eqLit) == LitValue::False) break;
                    TheoryLemma lemma;
                    for (auto& lit : *r) lemma.lits.push_back(lit.negated());
                    if (satMin) ConflictMinimizer::dedup(lemma.lits);
                    lemma.lits.push_back(eqLit.negated());   // ¬(A=B) = A≠B
                    if (lemmaDb.insertIfNew(lemma)) {
                        noPropEntailments_.push_back(std::move(lemma));
                        ++dBuffered;
                    }
                    break;   // one solver's proof suffices
                }
            }
        }
        if (std::getenv("XOLVER_L4R_DIAG") && (dQueried || dBuffered)) {
            std::fprintf(stderr, "[R2-DEMAND] queried=%zu buffered=%zu\n",
                         dQueried, dBuffered);
            std::fflush(stderr);
        }
    }

    for (size_t i = 0; i < solvers_.size(); ++i) {
        auto* solver = solvers_[i].get();
        if (!solver->supportsCombination()) continue;
        auto props = solver->getDeducedSharedEqualities();
        // At Full effort, augment with bounded atom-level Gaussian implied
        // equalities over the (few) array-index shared vars — catches index
        // equalities entailed by a linear COMBINATION of asserted equalities that
        // the per-atom same-form/2-var detectors miss (read2). Scoped to
        // array-index pairs + Full only (52b0510's anti-flood discipline).
        if (effort == TheoryEffort::Full && arrayIdxSet.size() >= 2) {
            std::vector<SharedTermId> idxVec(arrayIdxSet.begin(), arrayIdxSet.end());
            auto gauss = solver->deduceIndexEqualitiesByGaussian(idxVec);
            props.insert(props.end(),
                         std::make_move_iterator(gauss.begin()),
                         std::make_move_iterator(gauss.end()));
        }
        NO_DBG << "[NO] solver=" << (int)solver->id()
               << " deducedEqualities=" << props.size() << "\n";
        static const bool noDiag = xolver::env::diag("XOLVER_NO_DIAG");
        if (noDiag && !props.empty()) {
            size_t deferred = 0, arrayPair = 0;
            for (auto& p : props) {
                bool ina = arrayIdxSet.count(p.a), inb = arrayIdxSet.count(p.b);
                if (ina && inb) ++arrayPair;
                if (effort != TheoryEffort::Full && ina && inb) ++deferred;
            }
            std::fprintf(stderr, "[NO] solver=%d effort=%d deduced=%zu arrayPair=%zu deferred=%zu\n",
                         (int)solver->id(), (int)effort, props.size(), arrayPair, deferred);
            std::fflush(stderr);
        }
        // L4-reach: route array-relevant deduced shared eqs through the Standard
        // entailment channel (XOLVER_NIA_NO_PROP). The array-pair eqs are the
        // ~handful cs_*-class instances need to fire read-over-write; they are
        // otherwise deferred to Full (the lemma channel is dropped+cache-poisoned
        // at Standard), which huge formulas never reach. The entailment channel is
        // honored at Standard and the clause is the IDENTICAL globally-valid
        // (¬reasons ∨ eqLit) the Full lemma path emits. Sound: same reason
        // contract as Full (0-unsound there); relevancy = array-pair + caresPair,
        // an under-approximation (propagating fewer facts can only lose
        // completeness, never produce a wrong UNSAT).
        static const bool noProp = [] {
            return xolver::env::flag("XOLVER_NIA_NO_PROP");
        }();
        // PRE-PASS: buffer ALL array-pair entailments before the main loop. The
        // main loop returns on the first novel NON-array eq lemma, and the ~800
        // non-array eqs are ordered before the ~100 array pairs, so without this
        // dedicated pass the array pairs (the ones cs_* actually needs) are
        // starved for hundreds of cb_propagate rounds. Each clause is the SAME
        // globally-valid (¬reasons ∨ eqLit) the Full lemma path emits; routing it
        // via the entailment channel just makes CaDiCaL honor it at Standard.
        if (noProp && effort != TheoryEffort::Full) {
            size_t buffered = 0;
            for (auto& prop : props) {
                if (!(arrayIdxSet.count(prop.a) && arrayIdxSet.count(prop.b)))
                    continue;
                if (careGraphEnabled_ && !careGraph_.caresPair(prop.a, prop.b))
                    continue;
                SatLit eqLit =
                    registry_->getOrCreateSharedEqualityAtom(prop.a, prop.b);
                if (assignmentView_ &&
                    assignmentView_->value(eqLit) == LitValue::True) continue;
                TheoryLemma lemma;
                for (auto& reason : prop.reasons)
                    lemma.lits.push_back(reason.negated());
                if (satMin) ConflictMinimizer::dedup(lemma.lits);
                lemma.lits.push_back(eqLit);
                // lemmaDb.insertIfNew = backtrack-safe literal-set dedup, so each
                // clause is buffered (and added to CaDiCaL) exactly once.
                if (lemmaDb.insertIfNew(lemma)) {
                    noPropEntailments_.push_back(std::move(lemma));
                    ++buffered;
                }
            }
            static const bool l4rDiag = xolver::env::diag("XOLVER_L4R_DIAG");
            if (l4rDiag && buffered) {
                std::fprintf(stderr, "[L4R] solver=%d buffered=%zu total=%zu\n",
                             (int)solver->id(), buffered, noPropEntailments_.size());
                std::fflush(stderr);
            }
        }
        for (auto& prop : props) {
            // Defer array-index-pair deduced equalities to Full effort (see above).
            if (effort != TheoryEffort::Full &&
                arrayIdxSet.count(prop.a) && arrayIdxSet.count(prop.b)) {
                continue;
            }
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
            // ⚠️ UNSOUND research toggle (g_skipEufMergedUNSAFE, default-OFF). Skips
            // publishing a deduced equality EUF has already merged. This CONVERGES
            // the 444-round combination loop on the Zohar ground repro (hang ->
            // terminate) but is UNSOUND: the shared-eq atom is the inter-theory
            // conflict channel, so dropping it loses UNSAT detection -> WRONG-SAT
            // (reg gate: 8 unsat->sat). DO NOT enable in a shipped binary. Retained
            // only to reproduce the convergence mechanism for the eventual sound fix
            // (theory propagation that keeps the eq but propagates it efficiently).
            if (g_skipEufMergedUNSAFE) {
                auto eufIt = solverByTheory_.find(TheoryId::EUF);
                if (eufIt != solverByTheory_.end() &&
                    eufIt->second->sharedTermsMerged(prop.a, prop.b)) {
                    deducedEqCache_.insert(ReportedPropKey{solver->id(), prop.a, prop.b});
                    continue;
                }
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
            // Minimize (XOLVER_SAT_MIN) the reason side before appending the
            // implied-equality literal, then re-append: dedup must not drop the
            // (unique) consequent. Sound — the lemma's literal set is preserved.
            if (satMin) ConflictMinimizer::dedup(lemma.lits);
            lemma.lits.push_back(eqLit);
            NO_DBG << "[NO-RET-8] lemma=" << debug::fmtClause(lemma.lits) << "\n";
            if (lemmaDb.insertIfNew(lemma)) {
                if (g_combDiag) {
                    ++g_cd.dedEqLemma;
                    auto eufIt2 = solverByTheory_.find(TheoryId::EUF);
                    if (eufIt2 != solverByTheory_.end() &&
                        eufIt2->second->sharedTermsMerged(prop.a, prop.b))
                        ++g_cd.dedEqEufMerged;
                    else
                        ++g_cd.dedEqAtomFresh;
                }
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
    // XOLVER_COMB_MODEL_BASED, additionally the LIA-based non-convex combined
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
        const bool arrangeInternals = xolver::env::diag("XOLVER_COMB_ARRANGE_INTERNAL");
        for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
            const auto* st = sharedTermRegistry_->get(stId);
            if (!st) continue;
            if (!arrangeInternals && st->isInternal) continue;   // scope to user terms only by default
            std::optional<RealValue> v;
            // Numeric-constant shared terms: by default a constant-vs-variable
            // arrangement is skipped — splitting on it can destabilize array
            // axiom instantiation, and the variable's value coinciding with the
            // constant in this model does NOT make them required-equal. EXCEPTION:
            // under the demand-driven care graph (array-combination logics) a
            // constant that is an array INDEX must be arranged against a
            // same-valued index variable, or the Row1/Row2 read value stays
            // undetermined and the model is jointly inconsistent (alra_010: read
            // index i0 numerically equals the constant store index 1.0 but EUF
            // never merges them, so select(store(...,1.0,..),i0) is unconstrained).
            // The caresPair filter in the pairing loop admits only the index
            // pairs that matter; without the care graph we keep the conservative
            // skip. A bare constant has no simplex value, so take it from
            // constValue() directly.
            if (auto cv = sharedTermRegistry_->constValue(stId)) {
                if (!careGraphEnabled_) continue;
                v = RealValue::fromMpq(*cv);
            } else {
                for (auto& solver : solvers_) {
                    if (solver->id() == TheoryId::EUF) continue;
                    if (!solver->supportsCombination()) continue;
                    v = solver->sharedTermArithValue(stId);
                    if (v) break;
                }
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
                if (g_combDiag) ++g_cd.arrSplitValue;
                return TheoryCheckResult::mkLemma(std::move(lemma));
            }
        }
    }

    // Phase 2 — DEMAND-DRIVEN ARRANGEMENT (XOLVER_COMB_DEMAND_ARRANGE,
    // default-ON under arrayCombinationMode_, off otherwise).
    //
    // Background: the value-based arrangement above only fires for shared-
    // scalar pairs where SOME arith solver already has a model value AND the
    // two values coincide. For QF_ANIA / QF_AUFNIA this is a deadlock — NIA
    // cannot pick concrete index values without first knowing which compound
    // indices are equal (so the array reasoner can fire Row1 / Row2), but the
    // arrangement above never asks NIA about a pair whose value NIA does not
    // yet have. Result: 0 splits emitted, the array combination never closes.
    //
    // The principled Nelson-Oppen fix (matches cvc5 / Z3 combination):
    // enumerate care-graph pairs DIRECTLY and emit ONE arrangement split per
    // undecided + unmerged pair. The split lemma (a = b) ∨ ¬(a = b) is a
    // tautology, so sound by construction; SAT must commit one polarity, and
    // the per-pair dedup via emittedArrangementSplits_ bounds the total work
    // at O(|cared|^2) over the entire solve — NOT per call — so termination
    // is structural, not budget-based.
    //
    // Scope: arrayCombinationMode_ only. The non-array combination logics
    // (QF_UFNIA/QF_UFNRA) reach the same arrangement through their LIA / LRA
    // mirror's value-based splits and do not need (and should not pay for)
    // this enumeration. Internal / constant shared terms are filtered out
    // identically to the value-based loop (XOLVER_COMB_ARRANGE_INTERNAL
    // override for diagnostics).
    if (arrayCombinationMode_ && effort == TheoryEffort::Full &&
        sharedTermRegistry_ && registry_ && careGraphEnabled_) {
        static const bool demandEnabled = []() {
            const char* e = std::getenv("XOLVER_COMB_DEMAND_ARRANGE");
            // default ON under arrayCombinationMode_; explicit "=0" opts out.
            return !e || !(e[0] == '0' && e[1] == '\0');
        }();
        if (demandEnabled) {
            TheorySolver* eufSolverDD = nullptr;
            auto eufItDD = solverByTheory_.find(TheoryId::EUF);
            if (eufItDD != solverByTheory_.end()) eufSolverDD = eufItDD->second;

            const bool arrangeInternalsDD =
                xolver::env::diag("XOLVER_COMB_ARRANGE_INTERNAL");

            // Collect cared shared scalars. Bound: |cared| ≤ |all shared|.
            // emittedArrangementSplits_ ensures EACH pair is split at most
            // once over the whole solve, so the total split budget across
            // calls is O(|cared|^2 / 2) — purely structural.
            struct CaredScalar { SharedTermId id; SortId sort; };
            std::vector<CaredScalar> cared;
            cared.reserve(careGraph_.careCount());
            for (SharedTermId stId : sharedTermRegistry_->allSharedTerms()) {
                const auto* st = sharedTermRegistry_->get(stId);
                if (!st) continue;
                if (!arrangeInternalsDD && st->isInternal) continue;
                if (sharedTermRegistry_->constValue(stId)) continue;
                if (!careGraph_.cares(stId)) continue;
                cared.push_back({stId, st->sort});
            }
            for (size_t i = 0; i < cared.size(); ++i) {
                for (size_t j = i + 1; j < cared.size(); ++j) {
                    const auto& A = cared[i];
                    const auto& B = cared[j];
                    if (A.sort != B.sort) continue;
                    if (sharedEqMgr_.same(A.id, B.id)) continue;
                    if (sharedEqMgr_.diseqKnown(A.id, B.id)) continue;
                    if (eufSolverDD &&
                        eufSolverDD->sharedTermsMerged(A.id, B.id)) continue;

                    SharedTermId lo = A.id < B.id ? A.id : B.id;
                    SharedTermId hi = A.id < B.id ? B.id : A.id;
                    uint64_t key = (static_cast<uint64_t>(lo) << 32) |
                                   static_cast<uint64_t>(hi);
                    if (!emittedArrangementSplits_.insert(key).second) continue;

                    for (auto* owner : solversOwning(A.id, B.id)) {
                        owner->allowInterfaceDiseqModelBranch(A.id, B.id);
                    }
                    SatLit eqLit =
                        registry_->getOrCreateSharedEqualityAtom(A.id, B.id);
                    TheoryLemma lemma;
                    lemma.lits.push_back(eqLit);
                    lemma.lits.push_back(eqLit.negated());
                    NO_DBG << "[NO-DEMAND] split "
                           << stName(sharedTermRegistry_, A.id) << " = "
                           << stName(sharedTermRegistry_, B.id) << "\n";
                    if (g_combDiag) ++g_cd.arrSplitDemand;
                    return TheoryCheckResult::mkLemma(std::move(lemma));
                }
            }
        }
    }

    // Phase 1 (XOLVER_COMB_UFARG_ARRANGE, default ON): arrange unresolved UF-
    // argument congruences the scalar loop above cannot reach — the bridge-vars/
    // const args (internal or constant shared terms used as UF/select arguments)
    // that are value-equal to a sibling argument but not yet merged. EUF reports
    // the value-equal-but-not-merged arg pairs; emit a one-time a=b ∨ a≠b split
    // per pair. TERMINATION: the UF applications and (purification-created)
    // bridge vars are fixed pre-solve and arranging spawns no new pairs, so the
    // candidate set is finite and emittedArrangementSplits_ dedup bounds it.
    //
    // 2026-06-02 PROMOTE default-ON: closes Wisa-class false-Unknown floors in
    // QF_UFLIA. xs-05-08/12/16/20 all move unknown -> correct unsat. Unit
    // 1098/1098 + reg 670/670 unchanged, 0 unsound. Escape: XOLVER_COMB_UFARG_ARRANGE=0.
    auto ufargArrangeOn = []() {
        const char* e = std::getenv("XOLVER_COMB_UFARG_ARRANGE");
        if (!e) return true;
        return !(e[0] == '0' && e[1] == '\0');
    };
    if (effort == TheoryEffort::Full && combinationMode_ && sharedTermRegistry_ &&
        registry_ && ufargArrangeOn()) {
        TheorySolver* eufS = nullptr;
        auto it = solverByTheory_.find(TheoryId::EUF);
        if (it != solverByTheory_.end()) eufS = it->second;
        if (eufS) {
            for (auto& pr : eufS->collectArrangeableUfArgPairs(
                     [this](SharedTermId a, SharedTermId b) {
                         return sharedArgsArrangeable(a, b);
                     })) {
                SharedTermId a = pr.first, b = pr.second;
                if (a == b) continue;
                if (sharedEqMgr_.same(a, b) || sharedEqMgr_.diseqKnown(a, b)) continue;
                SharedTermId lo = a < b ? a : b, hi = a < b ? b : a;
                uint64_t key = (static_cast<uint64_t>(lo) << 32) |
                               static_cast<uint64_t>(hi);
                if (!emittedArrangementSplits_.insert(key).second) continue;
                for (auto* owner : solversOwning(a, b))
                    owner->allowInterfaceDiseqModelBranch(a, b);
                SatLit eqLit = registry_->getOrCreateSharedEqualityAtom(a, b);
                TheoryLemma lemma;
                lemma.lits.push_back(eqLit);
                lemma.lits.push_back(eqLit.negated());
                NO_DBG << "[NO-UFARG] split "
                       << stName(sharedTermRegistry_, a) << " = "
                       << stName(sharedTermRegistry_, b) << "\n";
                if (g_combDiag) ++g_cd.arrSplitUfarg;
                return TheoryCheckResult::mkLemma(std::move(lemma));
            }
        }
    }

    // Iter#28: if we deferred a Lemma at step 2 (XOLVER_COMB_PUBLISH_ON_LEMMA),
    // return it now — the shared-eq publish + arrangement above already ran
    // against the current trail. SAT receives the case-split AND any
    // propagated shared eqs in the same cb_propagate round.
    if (havePendingLemma) {
        NO_DBG << "[NO-RET-LEMMA-DEFERRED] returning saved Lemma after publish\n";
        return pendingLemma;
    }
    NO_DBG << "[NO-RET-9] Consistent\n";
    return TheoryCheckResult::consistent();
}

bool TheoryManager::sharedArgsArrangeable(SharedTermId a, SharedTermId b) const {
    if (a == b) return false;
    // DISEQUAL exclusion (the uflra_007 recovery): a (distinct a b) makes the
    // model coincidence a recoverable artifact, not a congruence obligation. In
    // combination mode such a disequality lives either as a shared-equality atom
    // decided FALSE (the usual route for Eq/Distinct over two shared terms) or in
    // sharedEqMgr_, OR — rarely — as a native arith disequality. Check all.
    // DISEQUAL exclusion (the uflra_007 recovery): the pair carries an asserted
    // disequality, so the model coincidence is a recoverable artifact (a valid
    // model separates them), not a congruence obligation. Sources, in order of
    // reliability at certificate time: a per-solver interface disequality
    // (sharedTermsActivelyDisequal — set for a combination (distinct a b)),
    // sharedEqMgr_, or a decided shared-eq atom (only if the assignment view is
    // available — it is not on the post-solve certificate path).
    bool disequal = sharedEqMgr_.diseqKnown(a, b);
    if (!disequal && registry_ && assignmentView_) {
        SatLit eqLit = registry_->getOrCreateSharedEqualityAtom(a, b);
        if (assignmentView_->value(eqLit) == LitValue::False) disequal = true;
    }
    std::optional<RealValue> va, vb;
    for (const auto& solver : solvers_) {
        if (solver->id() == TheoryId::EUF) continue;
        if (!solver->supportsCombination()) continue;
        if (!va) va = solver->sharedTermArithValue(a);
        if (!vb) vb = solver->sharedTermArithValue(b);
        if (solver->sharedTermsActivelyDisequal(a, b)) disequal = true;
    }
    return va && vb && (*va == *vb) && !disequal;
}

bool TheoryManager::hasCompleteSatCertificate(std::string* reason) const {
    // Positive completeness proof, fail-closed: certify only if EVERY registered
    // solver positively certifies its own completeness. A solver that cannot
    // (default satComplete()==false, or a fired obligation detector) blocks the
    // certificate, so the api floor downgrades the combination SAT to Unknown.
    for (const auto& solver : solvers_) {
        std::string r;
        if (!solver->satComplete(&r)) {
            if (reason) *reason = r;
            return false;
        }
    }
    // Phase 1 combination-arrangement conjunct: per-theory completeness is NOT
    // combination completeness. A same-function application pair whose differing
    // shared args COINCIDE in the model but are not merged leaves an undischarged
    // congruence (Wisa select_format(fmt1) ≅ select_format(k)) -> the model is
    // globally inconsistent (functional consistency forces the apps equal) ->
    // cannot certify. The arrangeability test is model-coincidence MINUS native
    // disequality (sharedArgsArrangeable): a pair carrying an asserted (distinct
    // a b) is excluded — the coincidence is a model artifact a valid model
    // separates, so the SAT verdict is recoverable (uflra_007 over-floor fix).
    for (const auto& solver : solvers_) {
        for (auto& pr : solver->collectArrangeableUfArgPairs(
                 [this](SharedTermId a, SharedTermId b) {
                     return sharedArgsArrangeable(a, b);
                 })) {
            // A pair the combination has already ARRANGED — committed equal or
            // DISEQUAL — is NOT pending. The decisive signal is the SAT
            // assignment of the pair's shared-equality atom: a DECIDED value
            // (True = arranged equal, False = arranged disequal, e.g. an asserted
            // (distinct a b) whose atom is assigned false) means the pair is
            // resolved. (sharedEqMgr only tracks interface (dis)eqs, missing an
            // arith-internal/SAT-level (distinct a b) — that over-floored
            // uflra_007.) Only an UNASSIGNED shared-eq atom is a genuine
            // undischarged arrangement obligation that blocks completeness.
            if (sharedEqMgr_.same(pr.first, pr.second)) continue;
            if (sharedEqMgr_.diseqKnown(pr.first, pr.second)) continue;
            if (assignmentView_ && registry_) {
                SatLit eqLit = registry_->getOrCreateSharedEqualityAtom(pr.first, pr.second);
                if (assignmentView_->value(eqLit) != LitValue::Unknown) continue;
            }
            if (reason) *reason = "combination: unarranged UF-argument congruence "
                                  "(shared bridge-var/arg value-equal but not merged)";
            return false;
        }
    }
    return true;
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

    // Track 3 (XOLVER_EUF_UF_MODEL): extend tokenToNum + numericAssignments for
    // opaque numeric scalars that still carry an unresolved "@e.." token after
    // the arith-backed remap. EUF tracks them only by eclass identity (no arith
    // value), so the validator's UFApply lookup against the EUF-built table
    // would never match the computed args. Mint a DISTINCT integer per distinct
    // unresolved token, avoiding numbers already claimed by constrained
    // scalars/literals (preserves disequalities); write into:
    //   - tokenToNum: so the toBare remap rewrites function-interp arg/value
    //     tokens to bare rationals.
    //   - numericAssignments: so the validator's typed channel computes the
    //     SAME value for the original-formula arg expression.
    // Sound: only ever turns a Satisfied into a Violated (over-floors) when a
    // constraint we missed exists; never the other way. Skips @CONFLICT tokens
    // (distinctness was already violated; leaving them opaque correctly defeats
    // the UFApply lookup -> Indeterminate -> floor). Gated on:
    //   - functionInterps non-empty (only matters for UF table consistency)
    //   - arrayInterps empty (array combination has axiom-pinned "unconstrained"
    //     scalars whose mint would falsify Row2 — alra_010 class; recovery there
    //     needs real array-aware model construction, not scalar minting).
    static const bool t3UfMint = xolver::env::diag("XOLVER_EUF_UF_MODEL");
    if (t3UfMint && !aggregated.functionInterps.empty() &&
        aggregated.arrayInterps.empty()) {
        std::unordered_set<long long> usedNums;
        auto noteRat = [&](const std::string& v) {
            std::string body = v.rfind("#n:", 0) == 0 ? v.substr(3) : v;
            if (body.empty()) return;
            try {
                mpq_class q(body);
                if (q.get_den() == 1 && q.get_num().fits_slong_p())
                    usedNums.insert(q.get_num().get_si());
            } catch (...) {}
        };
        for (const auto& [n, v] : aggregated.assignments) { (void)n; noteRat(v); }
        for (const auto& [tok, num] : tokenToNum)
            if (num != "@CONFLICT") noteRat(num);

        // Distinct unresolved opaque tokens reached via scalar assignments, with
        // the FIRST var name per token (deterministic) for numericAssignments.
        std::vector<std::pair<std::string, std::string>> mintTargets;
        std::unordered_set<std::string> seenTok;
        for (const auto& [name, val] : aggregated.assignments) {
            if (val.empty() || val[0] != '@') continue;
            if (tokenToNum.count(val)) continue;
            if (!seenTok.insert(val).second) continue;
            mintTargets.push_back({val, name});
        }
        long long nextFree = 0;
        for (const auto& [tok, name] : mintTargets) {
            while (usedNums.count(nextFree)) ++nextFree;
            long long v = nextFree++;
            usedNums.insert(v);
            std::string canon = "#n:" + std::to_string(v);
            tokenToNum.emplace(tok, canon);
            try {
                aggregated.numericAssignments.emplace(
                    name, RealValue::fromMpq(mpq_class(std::to_string(v))));
            } catch (...) {}
        }

        // Chain-mint: opaque tokens that appear inside functionInterps but are
        // NOT var-backed (UF-application class tokens). Without this, a chained
        // f(g(x)) table -- where g's interp value is "@e.." and f's interp arg
        // is "@e.." -- can't bridge: the validator's recursive eval gets g(x)=N
        // via the table (g's value resolved), then looks up f's table with arg=N
        // but the entry key is still "@e..". Minting distinct numbers per
        // distinct chain token (preserving disequality) keeps the table
        // internally consistent so f's entry now keys on the SAME number g
        // returned. tokenToNum-only (no var name to backfill numericAssignments).
        std::vector<std::string> chainTokens;
        std::unordered_set<std::string> seenChain;
        auto consider = [&](const std::string& s) {
            if (s.empty() || s[0] != '@') return;
            if (tokenToNum.count(s)) return;
            if (!seenChain.insert(s).second) return;
            chainTokens.push_back(s);
        };
        for (const auto& [fname, fi] : aggregated.functionInterps) {
            (void)fname;
            for (const auto& e : fi.entries) {
                for (const auto& a : e.args) consider(a);
                consider(e.value);
            }
            consider(fi.deflt);
        }
        for (const auto& tok : chainTokens) {
            while (usedNums.count(nextFree)) ++nextFree;
            long long v = nextFree++;
            usedNums.insert(v);
            tokenToNum.emplace(tok, "#n:" + std::to_string(v));
        }
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

    // Track 3 (XOLVER_EUF_UF_MODEL): remap token-keyed UF interpretations to the
    // bare-rational keys ArithModelValidator expects. The validator evaluates
    // each UFApply argument to mpq::get_str() and matches entry.args EXACTLY, so
    // arg/value tokens must become bare:
    //   - remap() turns an opaque "@e.." into "#n:<rat>" when that class has a
    //     UNIQUE arith value (conflict-/distinctness-guarded above); we then strip
    //     the "#n:" prefix.
    //   - a numeric-literal token "#n:.." strips directly; bool "#b:1"/"#b:0" ->
    //     "1"/"0"; an opaque token with no resolved number stays "@e.." (its
    //     entry then never matches a Number arg — harmless, falls to deflt).
    // CMS-format interps (already bare rationals) pass through unchanged (the
    // remap is idempotent on a bare rational). No-op when no function interps.
    if (!aggregated.functionInterps.empty()) {
        auto toBare = [&](std::string& v) {
            remap(v);
            if (v.rfind("#n:", 0) == 0) v = v.substr(3);
            else if (v == "#b:1") v = "1";
            else if (v == "#b:0") v = "0";
        };
        std::vector<std::string> dropFns;
        const bool diagFi = xolver::env::diag("XOLVER_DIAG_FI");
        for (auto& [fname, fi] : aggregated.functionInterps) {
            for (auto& e : fi.entries) {
                for (auto& a : e.args) toBare(a);
                toBare(e.value);
            }
            toBare(fi.deflt);
            // Soundness backstop: if after the remap two entries share an identical
            // argument tuple but disagree on the value, the table is not a function
            // (distinct EUF classes collapsed onto one arith number despite the
            // @CONFLICT guard — e.g. a literal token vs an opaque token). Drop the
            // whole interp so the validator floors (Indeterminate) rather than
            // confirming against an inconsistent table.
            bool inconsistent = false;
            for (size_t i = 0; i < fi.entries.size() && !inconsistent; ++i)
                for (size_t j = i + 1; j < fi.entries.size(); ++j)
                    if (fi.entries[i].args == fi.entries[j].args &&
                        fi.entries[i].value != fi.entries[j].value) {
                        if (diagFi) std::fprintf(stderr,
                            "[FI-CONFLICT] %s args=[", fname.c_str());
                        if (diagFi) {
                            for (auto& a : fi.entries[i].args)
                                std::fprintf(stderr, "%s,", a.c_str());
                            std::fprintf(stderr, "] vals=%s vs %s\n",
                                fi.entries[i].value.c_str(),
                                fi.entries[j].value.c_str());
                        }
                        inconsistent = true; break;
                    }
            if (diagFi) std::fprintf(stderr,
                "[FI] %s entries=%zu inconsistent=%d\n",
                fname.c_str(), fi.entries.size(), inconsistent?1:0);
            if (inconsistent) dropFns.push_back(fname);
        }
        for (const auto& f : dropFns) aggregated.functionInterps.erase(f);
    }

    // ---- Unconstrained-scalar model completion (numericAssignments backfill) ----
    // A shared scalar that EUF tracks but no arith theory constrains stays an
    // opaque EUF token ("@e..") after the arith-backed remap above. The validator
    // does mpq_class on the string channel (fails -> defaults the scalar to 0,
    // collapsing i != j into 0 = 0 -> Violated) and the typed numericAssignments
    // channel it PREFERS is empty for them -> strict-validation flips
    // (auflia_004 / alia_005 class). Mint a DISTINCT integer per distinct token
    // into BOTH channels, and rewrite the SAME tokens in the array interps, so a
    // scalar and the array slot it indexes share one token space.
    //
    // Sound: minted values respect every EUF (dis)equality — same token -> same
    // value (preserves equalities), distinct tokens -> distinct values and the
    // mint avoids every already-assigned number (preserves disequalities, incl.
    // with arith-constrained scalars) — so no spurious (dis)equality is added.
    // The validator then confirms instead of seeing Indeterminate. Numeric sorts
    // only; uninterpreted/Bool tokens keep their own model channels (A3 lane).
    //
    // Gated by XOLVER_COMB_SCALAR_BACKFILL (default OFF, intent default-ON at
    // integration): a RECOVERY change validated against A5's strict-validation
    // build. Flag OFF => getModel byte-identical to before.
    if (sharedTermRegistry_ && std::getenv("XOLVER_COMB_SCALAR_BACKFILL")) {
        const CoreIr* ir = sharedTermRegistry_->coreIr();
        std::unordered_map<std::string, bool> numericScalar;
        if (ir) {
            for (SharedTermId st : sharedTermRegistry_->allSharedTerms()) {
                const auto* s = sharedTermRegistry_->get(st);
                if (!s || s->name.empty()) continue;
                auto sk = ir->sortKind(s->sort);
                if (sk && (*sk == SortKind::Int || *sk == SortKind::Real))
                    numericScalar[s->name] = true;
            }
        }

        // Integers already claimed by a resolved number (plain arith form "3" or
        // canonical "#n:3"); minted values must avoid these to keep disequalities
        // with constrained scalars.
        std::unordered_set<long long> usedNums;
        auto noteNum = [&](const std::string& v) {
            std::string body;
            if (v.rfind("#n:", 0) == 0) body = v.substr(3);
            else if (!v.empty() && (std::isdigit((unsigned char)v[0]) || v[0] == '-')) body = v;
            else return;
            try {
                mpq_class q(body);
                if (q.get_den() == 1 && q.get_num().fits_slong_p())
                    usedNums.insert(q.get_num().get_si());
            } catch (...) {}
        };
        for (auto& [n, v] : aggregated.assignments) { (void)n; noteNum(v); }
        for (auto& [n, ai] : aggregated.arrayInterps) {
            (void)n; noteNum(ai.defaultVal);
            for (auto& [ix, el] : ai.entries) { noteNum(ix); noteNum(el); }
        }

        long long nextFree = 0;
        std::unordered_map<std::string, std::string> mint;  // token -> "#n:<int>"
        auto mintFor = [&](const std::string& tok) -> const std::string& {
            auto it = mint.find(tok);
            if (it != mint.end()) return it->second;
            while (usedNums.count(nextFree)) ++nextFree;
            long long v = nextFree++;
            usedNums.insert(v);
            return mint.emplace(tok, "#n:" + std::to_string(v)).first->second;
        };

        // Numeric scalars carrying an opaque token: backfill ONLY the typed
        // numericAssignments channel (which A5's validator prefers). We do NOT
        // rewrite the string `assignments` channel nor the array-interp tokens:
        // feeding minted concrete values into those exposed an invalid model for
        // genuinely array-axiom-constrained "unconstrained" scalars (self-store
        // cases like alra_010: i0/e0 are pinned by a=store(a,i0,e0), so distinct
        // minting violates Row2 and the array soundness gate correctly downgrades
        // to Unknown — a sat->unknown regression). Restricting to the typed
        // channel lets the validator confirm scalar (dis)equalities (e.g. i!=j)
        // without perturbing the array-read evaluation. Recovering the self-store
        // array reads needs real array-aware model construction (A3 lane), not
        // scalar minting.
        for (auto& [name, val] : aggregated.assignments) {
            if (val.empty() || val[0] != '@') continue;      // opaque tokens only
            if (!numericScalar.count(name)) continue;         // numeric sorts only
            if (aggregated.numericAssignments.count(name)) continue;  // already typed
            const std::string& num = mintFor(val);
            try {
                aggregated.numericAssignments.emplace(
                    name, RealValue::fromMpq(mpq_class(num.substr(3))));
            } catch (...) {}
        }
    }

    if (aggregated.assignments.empty() && aggregated.numericAssignments.empty() &&
        aggregated.functionInterps.empty() && aggregated.arrayInterps.empty())
        return std::nullopt;
    return aggregated;
}

} // namespace xolver
