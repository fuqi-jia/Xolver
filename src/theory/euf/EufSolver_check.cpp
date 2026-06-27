#include <cstdlib>
#include "util/EnvParam.h"
#include <chrono>
#include "theory/euf/EufSolver.h"
#include "util/SolveClock.h"
#ifdef XOLVER_ENABLE_PROOFS
#include "proof/TheoryProofSink.h"
#include "theory/core/TheoryAtomRegistry.h"
#endif
#include <stdexcept>
#include "theory/array/AniaProfile.h"
#include "theory/combination/CareGraph.h"
#include "theory/core/DebugTrace.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/datatype/DtModelValidator.h"
#include "expr/ir.h"
#include <cassert>
#include <algorithm>
#include <functional>
#include <climits>
#include <map>
#include <optional>
#include <tuple>

namespace xolver {

// NOTE: This translation unit was split out of EufSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

#ifdef XOLVER_ENABLE_PROOFS
void EufSolver::pushEufTransitivityCert(const std::vector<SatLit>& reasons) {
    // Record the conflict literals (asserted equality chain + the conclusion
    // disequality, which is the last reason: a (= l r) atom asserted FALSE) by IR
    // id and polarity, with rule eq_transitive. The Solver's union-find self-check
    // then keeps only true transitivity conflicts. Congruence-involved conflicts
    // carry the same shape but fail that check and stay skeleton.
    auto* sink = proof::activeProofSink();
    if (!sink || !eqAtomRegistry_) return;
    proof::TheoryConflictCert cert;
    cert.rule = "eq_transitive";
    for (SatLit lit : reasons) {
        const TheoryAtomRecord* rec = eqAtomRegistry_->findBySatVar(lit.var);
        if (!rec) return;  // can't identify the atom -> emit none (skeleton)
        cert.lits.push_back({rec->exprId, lit.sign});
    }
    if (!cert.lits.empty()) sink->addConflict(std::move(cert));
}

void EufSolver::pushBoolCongruenceCert(const std::vector<SatLit>& reasons) {
    // A Bool e-class became both true and false. The reasons explain the chain
    // trueTerm ≡ predTrue, predTrue ≡ predFalse (by congruence), predFalse ≡
    // falseTerm. Record every reason by IR id + asserted polarity, tagged
    // "bool_congruence"; the Solver classifies them (Eq leaf equalities vs the two
    // predicate atoms) and reconstructs the predicate-congruence refutation. The
    // true/false constant merges themselves carry NO SatLit reason (they are
    // structural), so the reason list is exactly {predicate-true literal,
    // predicate-false literal, leaf equalities} — precisely what the proof needs.
    auto* sink = proof::activeProofSink();
    if (!sink || !eqAtomRegistry_) return;
    proof::TheoryConflictCert cert;
    cert.rule = "bool_congruence";
    for (SatLit lit : reasons) {
        const TheoryAtomRecord* rec = eqAtomRegistry_->findBySatVar(lit.var);
        if (!rec) return;  // can't identify the atom -> emit none (skeleton)
        cert.lits.push_back({rec->exprId, lit.sign});
    }
    if (!cert.lits.empty()) sink->addConflict(std::move(cert));
}
#endif

TheoryCheckResult EufSolver::check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    aniaprof::init();
    aniaprof::Scope _profCheck(aniaprof::EUF_CHECK);
    auto _checkT0 = hotProfileEnabled_ ? std::chrono::steady_clock::now()
                                       : std::chrono::steady_clock::time_point{};
    if (hotProfileEnabled_) {
        ++hotProfile_.checkCalls;
        // Periodic dump so a SIGKILL'd timeout still produces signal. Every
        // 1000 checks (low-overhead even on QG-class with 1e6 checks).
        if (hotProfile_.checkCalls % 1000 == 0) {
            std::cerr << "[EUF-HOTPROFILE@" << hotProfile_.checkCalls << "]"
                      << " checkUs=" << hotProfile_.checkUs
                      << " saturationUs=" << hotProfile_.saturationUs
                      << " entailUs=" << hotProfile_.entailmentUs
                      << " registerSigUs=" << hotProfile_.registerSigUs
                      << " merges=" << hotProfile_.mergesProcessed
                      << " entailEmitted=" << hotProfile_.entailmentEmitted
                      << std::endl;  // flush so SIGKILL'd progress is preserved
        }
    }
    struct _CheckGuard {
        bool en; std::chrono::steady_clock::time_point t0; EufHotProfile* p;
        ~_CheckGuard() {
            if (en) p->checkUs += std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - t0).count();
        }
    } _g{hotProfileEnabled_, _checkT0, &hotProfile_};
    if (pendingUnknown_) {
        return TheoryCheckResult::unknown();
    }
    if (pendingConflict_) {
        return TheoryCheckResult::mkConflict(*pendingConflict_);
    }

    if (std::getenv("EUF_VERIFY")) {
        int stale = debugCountStaleMerges();
        if (stale > 0)
            fprintf(stderr, "[STALE_MERGE@check] count=%d records=%zu trail=%zu\n",
                    stale, egraph_.mergeRecordCount(), trail_.size());
    }

    // Array Row1/Const eager merges + signature registration produce
    // tautological / congruence consequences at the current decision level.
    // Tag them with currentLevel_ so the level-ordered saturation places them
    // after all lower-level merges.
    // Array axiom enqueue: Row1/Const/Row2-const eager merges (enqueueEagerMerges)
    // + L2 Row2-cond merges for KNOWN-disequal index pairs (ArrayRow2Cond carries
    // the diseq reason + i~lhs/j~rhs chains so conflicts are sound). Factored into
    // a lambda so the L3 fixpoint (after saturation) can re-run it — nested
    // read-over-write (e.g. (Array Int (Array Int Int))) needs the OUTER peel's
    // congruence closed before the INNER reads become peelable.
    auto enqueueArrayAxioms = [&]() {
        if (!arrayMode_) return;
        ensureArrayContext();
        if (!arrayReasoner_.active()) return;
        arrayReasoner_.enqueueEagerMerges(mergeQueue_);
        // #75 store-store no-op merge (gated default-OFF, level-tagged so backtrack
        // removes it). Conditional on s1~s2 + distinct const indices, so unlike the
        // tautology eager merges it carries currentLevel_.
        arrayReasoner_.enqueueStoreNoopMerges(currentLevel_, mergeQueue_);
        if (arrayReasoner_.row2DiseqEnabled()) {
            auto repPairKey = [](EClassId a, EClassId b) -> uint64_t {
                uint32_t lo = a < b ? a : b, hi = a < b ? b : a;
                return (static_cast<uint64_t>(lo) << 32) | hi;
            };
            std::unordered_map<uint64_t, const ActiveDisequality*> diseqMap;
            diseqMap.reserve(disequalities_.size() + sharedDisequalities_.size() + 1);
            for (const auto& d : disequalities_)
                diseqMap[repPairKey(egraph_.rep(d.lhs), egraph_.rep(d.rhs))] = &d;
            for (const auto& d : sharedDisequalities_)
                diseqMap[repPairKey(egraph_.rep(d.lhs), egraph_.rep(d.rhs))] = &d;
            // L11 demand-driven disequality (XOLVER_NIA_ROW2_DEMAND, default-OFF):
            // when an eligible Row2-cond pair (i,j) has NO known diseq, buffer it
            // (mapped to shared terms) so the combination layer can drive the arith
            // diseq prover on exactly this pair. Read once; capping via row2DemandSeen_.
            static const bool row2Demand = [] {
                return xolver::env::flag("XOLVER_NIA_ROW2_DEMAND");
            }();
            auto bufferDemand = [&](EufTermId i, EufTermId j) {
                if (!row2Demand || !sharedTermRegistry_) return;
                ExprId ei = termManager_.node(i).origin;
                ExprId ej = termManager_.node(j).origin;
                if (ei == NullExpr || ej == NullExpr) return;
                auto sa = sharedTermRegistry_->findByExprId(ei);
                auto sb = sharedTermRegistry_->findByExprId(ej);
                if (!sa || !sb || *sa == *sb) return;
                SharedTermId lo = *sa < *sb ? *sa : *sb, hi = *sa < *sb ? *sb : *sa;
                uint64_t key = (static_cast<uint64_t>(lo) << 32) | hi;
                if (!row2DemandSeen_.insert(key).second) return;   // already demanded
                row2DemandPairs_.push_back({lo, hi});
            };
            auto queryDiseq = [&](EufTermId i, EufTermId j)
                    -> std::optional<ArrayReasoner::Row2CondDiseq> {
                EClassId ri = egraph_.rep(i), rj = egraph_.rep(j);
                if (ri == rj) return std::nullopt;
                auto it = diseqMap.find(repPairKey(ri, rj));
                if (it == diseqMap.end()) { bufferDemand(i, j); return std::nullopt; }
                const ActiveDisequality& d = *it->second;
                EClassId rl = egraph_.rep(d.lhs), rr = egraph_.rep(d.rhs);
                if (rl == ri && rr == rj)
                    return ArrayReasoner::Row2CondDiseq{d.lhs, d.rhs, d.reason};
                if (rl == rj && rr == ri)
                    return ArrayReasoner::Row2CondDiseq{d.rhs, d.lhs, d.reason};
                return std::nullopt;   // rep moved since map build — skip (sound)
            };
            arrayReasoner_.enqueueRow2CondMerges(queryDiseq, currentLevel_, mergeQueue_);
        }
    };
    size_t mqTagFrom = mergeQueue_.size();
    enqueueArrayAxioms();
    // Register signatures for all newly interned terms before entering the
    // saturation loop.  This ensures late-interned terms (e.g. f(a) after a=b
    // has already been merged) are visible to congruence detection.
    {
        auto _rt0 = hotProfileEnabled_ ? std::chrono::steady_clock::now()
                                       : std::chrono::steady_clock::time_point{};
        egraph_.registerPendingSignatures(mergeQueue_);
        if (hotProfileEnabled_) hotProfile_.registerSigUs +=
            std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - _rt0).count();
    }
    for (size_t i = mqTagFrom; i < mergeQueue_.size(); ++i) mergeQueue_[i].level = currentLevel_;

    // XOLVER_UF_DISEQ_WATCH: index active disequalities by endpoint term so the
    // saturation loop can check, after each merge, only the disequalities that
    // touch the just-merged class (instead of re-scanning all of them).
    if (diseqWatchEnabled_) {
        rebuildDiseqIndex();
    }

    // Saturation loop, processed in ASCENDING decision-level order so the
    // egraph's size-based undo trail stays level-monotonic (interface-equality
    // merges can be injected out of record order; level order is the invariant
    // backtrack relies on). At each level transition we record an egraph
    // boundary = the state before that level's merges, which backtrack restores.
    int processingLevel = INT_MIN;
    // Process one pending merge at its decision level L. `pushCong` re-enqueues
    // each congruence this merge spawns (tagged with L). Returns nullopt to keep
    // draining, or a TheoryCheckResult to early-return (unknown / conflict).
    // Shared by both drivers below so the two paths are behaviourally identical;
    // only the queue data structure differs.
    auto applyMerge = [&](PendingMerge req, auto&& pushCong)
                          -> std::optional<TheoryCheckResult> {
        const int L = req.level;

        if (egraph_.same(req.a, req.b)) return std::nullopt;

        // sort check
        const auto& na = termManager_.node(req.a);
        const auto& nb = termManager_.node(req.b);
        if (na.sort != nb.sort && na.sort != NullSort && nb.sort != NullSort) {
            pendingUnknown_ = true;
            return TheoryCheckResult::unknown();
        }

        if (L != processingLevel) {
            recordEgraphBoundary(L);
            processingLevel = L;
        }

        // Apply the merge into a fresh side-queue so the congruences it spawns
        // can be tagged with this merge's level before re-entering the queue.
        std::deque<PendingMerge> cong;
        auto mr = egraph_.merge(req.a, req.b, req.reason, L, cong);
        for (auto& c : cong) { c.level = L; pushCong(std::move(c)); }
        if (!mr.merged) return std::nullopt;

        // Evaluate builtin constants in affected parent terms. Skip entirely
        // when no "#builtin.*" symbol exists (e.g. pure QF_UF): the loop below
        // can never fold anything, and collecting the whole merged-class
        // membership × parents on every merge is otherwise an O(class·parents)
        // cost per merge — a primary cause of the QF_UF scaling cliff.
        if (termManager_.hasBuiltinSymbols()) {
            std::vector<EufTermId> toEval;
            auto addParents = [&](EufTermId t) {
                for (EufTermId p : termManager_.parentsOf(t)) {
                    toEval.push_back(p);
                }
            };
            addParents(req.a);
            addParents(req.b);
            for (EufTermId member : egraph_.classMembers(mr.kept)) {
                addParents(member);
            }
            for (EufTermId member : egraph_.classMembers(mr.killed)) {
                addParents(member);
            }
            std::sort(toEval.begin(), toEval.end());
            toEval.erase(std::unique(toEval.begin(), toEval.end()), toEval.end());
            for (EufTermId p : toEval) {
                tryEvaluateBuiltin(p, L);
            }
        }

        // ITE metadata：只 enqueue，不递归 merge
        onEclassMerged(mr.kept, mr.killed);
        if (pendingConflict_) {
            return TheoryCheckResult::mkConflict(*pendingConflict_);
        }

        // XOLVER_UF_DISEQ_WATCH: only the members of the loser class (mr.killed)
        // had their representative change to mr.kept, so a disequality can become
        // violated only if one of its endpoint terms lives in that loser class.
        // Check those eagerly — the conflict is reported the moment it forms.
        // explainEquality is sound mid-saturation now (N-O proof forest walks the
        // actual merge path; level-aware backtrack keeps the egraph consistent).
        if (diseqWatchEnabled_) {
            for (EufTermId t : egraph_.classMembers(mr.killed)) {
                auto it = diseqByTerm_.find(t);
                if (it == diseqByTerm_.end()) continue;
                for (const auto& [idx, which] : it->second) {
                    const ActiveDisequality& d =
                        (which == 0) ? disequalities_[idx] : sharedDisequalities_[idx];
                    if (egraph_.same(d.lhs, d.rhs)) {
                        checkProofForestInvariants("DISEQ_WATCH-fire");
                        pendingConflict_ = buildDiseqConflict(d);
                        return TheoryCheckResult::mkConflict(*pendingConflict_);
                    }
                }
            }
        }
        // refreshCongruence is now handled inside merge()
        return std::nullopt;
    };

    auto _satT0 = hotProfileEnabled_ ? std::chrono::steady_clock::now()
                                     : std::chrono::steady_clock::time_point{};
    {
    aniaprof::Scope _profSat(aniaprof::EUF_SATURATE);
    if (!minLevelHeapEnabled_) {
        // Baseline: O(n) linear min-level scan + O(n) erase per pop (byte-identical
        // to the historical loop). Congruences append to mergeQueue_.
        // Wall-clock guard: a heavy array+UF congruence saturation (e.g. the
        // s3_srvr/s3_clnt AUFNIA cases, 680 KB of array+UF ops) is a single long
        // EUF check() the CaDiCaL-callback entry guards cannot interrupt. Throwing
        // yields control: the top-level checkSat firewall converts the escaping
        // std::exception to a sound Unknown (verified to propagate through CaDiCaL's
        // callback). Checked every 1024 merges; default-inert unless a deadline is
        // set and has passed (XOLVER_WALLCLOCK_MS).
        size_t _satScan = 0;
        while (!mergeQueue_.empty()) {
            if (((++_satScan & 0x3FF) == 0) && wall::hasDeadline() && wall::remainingMs() == 0)
                throw std::runtime_error("wall-clock deadline (EUF saturation)");
            // Pick the minimum-level pending merge (earliest at that level).
            size_t mi = 0;
            for (size_t i = 1; i < mergeQueue_.size(); ++i)
                if (mergeQueue_[i].level < mergeQueue_[mi].level) mi = i;
            PendingMerge req = mergeQueue_[mi];
            mergeQueue_.erase(mergeQueue_.begin() + static_cast<long>(mi));
            if (hotProfileEnabled_) ++hotProfile_.mergesProcessed;
            auto r = applyMerge(std::move(req),
                                [&](PendingMerge c) { mergeQueue_.push_back(std::move(c)); });
            if (r) {
                if (hotProfileEnabled_) hotProfile_.saturationUs +=
                    std::chrono::duration_cast<std::chrono::microseconds>(
                        std::chrono::steady_clock::now() - _satT0).count();
                return *r;
            }
        }
    } else {
        // XOLVER_EUF_MINLEVEL_HEAP: level-bucketed drain. begin() is the minimum
        // level; each bucket is FIFO so the per-level order matches the baseline's
        // "earliest at that level". O(n log L) total (L = #distinct levels) vs the
        // baseline's O(n^2). Congruences spawned at level L (the current minimum)
        // re-enter byLevel[L], so they are processed before any higher level —
        // identical ordering to the linear scan's global-min re-pick.
        std::map<int, std::deque<PendingMerge>> byLevel;
        // Absorb any merges sitting in mergeQueue_ into the level buckets. Called
        // initially AND after every applyMerge, because some merges are pushed to
        // mergeQueue_ DIRECTLY (not via pushCong) from inside the merge body —
        // notably tryEvaluateBuiltin's BuiltinEval folds (level 0). The baseline
        // linear scan would re-pick those by global-min; absorbing keeps the map
        // path behaviourally identical and source-agnostic.
        auto absorb = [&]() {
            if (mergeQueue_.empty()) return;
            for (auto& m : mergeQueue_) byLevel[m.level].push_back(std::move(m));
            mergeQueue_.clear();
        };
        absorb();
        auto pushCong = [&](PendingMerge c) { byLevel[c.level].push_back(std::move(c)); };
        size_t _satScan2 = 0;
        while (!byLevel.empty()) {
            if (((++_satScan2 & 0x3FF) == 0) && wall::hasDeadline() && wall::remainingMs() == 0)
                throw std::runtime_error("wall-clock deadline (EUF saturation)");
            auto it = byLevel.begin();
            PendingMerge req = std::move(it->second.front());
            it->second.pop_front();
            if (it->second.empty()) byLevel.erase(it);
            if (hotProfileEnabled_) ++hotProfile_.mergesProcessed;
            auto r = applyMerge(std::move(req), pushCong);
            if (r) {
                if (hotProfileEnabled_) hotProfile_.saturationUs +=
                    std::chrono::duration_cast<std::chrono::microseconds>(
                        std::chrono::steady_clock::now() - _satT0).count();
                return *r;
            }
            absorb();
        }
    }
    }  // end EUF_SATURATE profiling scope
    if (hotProfileEnabled_) hotProfile_.saturationUs +=
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - _satT0).count();

    // L3 (XOLVER_AX_FIXPOINT, default-OFF): array-axiom saturation FIXPOINT. The
    // main loop above ran the array passes ONCE (pre-saturation). For NESTED
    // arrays (e.g. (Array Int (Array Int Int))) the OUTER store peel only resolves
    // after congruence closure, exposing INNER reads that need their own peel.
    // Re-run the array axioms now (egraph is congruence-closed) and re-saturate;
    // repeat until no new merge (fixpoint) or the iteration backstop. The egraph
    // grows monotonically (internSelect dedups, same-class skips), so this
    // converges; kMaxAxIter is only a non-termination backstop (a hit means a bug
    // to fix, not a verdict cap — remaining merges re-derive next check). Sound:
    // the re-run merges are the same tautological / ArrayRow2Cond merges, stamped
    // at currentLevel_ so backtrack removes them.
    static const bool axDiagL3 = xolver::env::diag("XOLVER_AX_DIAG");
    if (axDiagL3)
        std::fprintf(stderr, "[L3] reach fixpoint-gate: en=%d arrayMode=%d active=%d\n",
                     arrayFixpointEnabled_ ? 1 : 0, arrayMode_ ? 1 : 0,
                     arrayReasoner_.active() ? 1 : 0);
    if (arrayFixpointEnabled_ && arrayMode_ && arrayReasoner_.active()) {
        const int kMaxAxIter = 64;
        for (int axIter = 0; axIter < kMaxAxIter; ++axIter) {
            size_t mark = mergeQueue_.size();          // drained == 0
            enqueueArrayAxioms();
            egraph_.registerPendingSignatures(mergeQueue_);
            for (size_t i = mark; i < mergeQueue_.size(); ++i)
                mergeQueue_[i].level = currentLevel_;
            if (axDiagL3)
                std::fprintf(stderr, "[L3] axIter=%d added=%zu\n", axIter, mergeQueue_.size() - mark);
            if (mergeQueue_.size() == mark) break;     // fixpoint: nothing new
            if (diseqWatchEnabled_) rebuildDiseqIndex();
            // Drain the newly-enqueued merges (baseline min-level order), reusing
            // applyMerge (still in scope). A conflict returns immediately.
            while (!mergeQueue_.empty()) {
                size_t mi = 0;
                for (size_t i = 1; i < mergeQueue_.size(); ++i)
                    if (mergeQueue_[i].level < mergeQueue_[mi].level) mi = i;
                PendingMerge req = mergeQueue_[mi];
                mergeQueue_.erase(mergeQueue_.begin() + static_cast<long>(mi));
                auto r = applyMerge(std::move(req),
                    [&](PendingMerge c) { mergeQueue_.push_back(std::move(c)); });
                if (r) return *r;
            }
            if (axIter == kMaxAxIter - 1 && std::getenv("XOLVER_AX_DIAG"))
                std::fprintf(stderr, "[L3] array fixpoint hit kMaxAxIter=%d (non-convergence?)\n",
                             kMaxAxIter);
        }
    }

    // true/false conflict
    if (trueTerm_ != NullEufTerm && falseTerm_ != NullEufTerm &&
        egraph_.same(trueTerm_, falseTerm_)) {
        auto er = egraph_.explainEquality(trueTerm_, falseTerm_);
        if (xolver::env::diag("EUF_DIAG")) {
            std::cerr << "[EUF-DIAG] TRUE-FALSE-conflict ok=" << er.ok
                      << " chain=" << er.reasons.size() << "\n";
        }
        if (er.ok) {
#ifdef XOLVER_ENABLE_PROOFS
            pushBoolCongruenceCert(er.reasons);
#endif
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
        }
        if (xolver::env::diag("EUF_DIAG")) {
            std::cerr << "[EUF_EXPLAIN_FAIL] true=false same=" << egraph_.same(trueTerm_, falseTerm_)
                      << " activeReasons=" << allActiveReasons().size() << "\n";
        }
        return TheoryCheckResult::mkConflict(TheoryConflict{allActiveReasons()});
    }

    // disequality conflicts
    for (const auto& d : disequalities_) {
        if (egraph_.same(d.lhs, d.rhs)) {
            auto er = egraph_.explainEquality(d.lhs, d.rhs);
            if (xolver::env::diag("EUF_DIAG")) {
                std::cerr << "[EUF-DIAG] diseq-conflict lhs=" << d.lhs << " rhs=" << d.rhs
                          << " ok=" << er.ok << " chain=" << er.reasons.size() << " reasons=";
                for (auto l : er.reasons) std::cerr << (l.sign?"":"-") << l.var << " ";
                std::cerr << " diseqReason=" << (d.reason.sign?"":"-") << d.reason.var << "\n";
            }
            if (er.ok) {
                er.reasons.push_back(d.reason);
#ifdef XOLVER_ENABLE_PROOFS
                pushEufTransitivityCert(er.reasons);
#endif
                return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
            }
            if (xolver::env::diag("EUF_DIAG")) {
                std::cerr << "[EUF_EXPLAIN_FAIL] diseq lhs=" << d.lhs << " rhs=" << d.rhs
                          << " same=" << egraph_.same(d.lhs, d.rhs)
                          << " activeReasons=" << allActiveReasons().size() << "\n";
            }
            auto reasons = allActiveReasons();
            reasons.push_back(d.reason);
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
        }
    }

    // shared disequality conflicts
    for (const auto& d : sharedDisequalities_) {
        if (egraph_.same(d.lhs, d.rhs)) {
            auto er = egraph_.explainEquality(d.lhs, d.rhs);
            if (xolver::env::diag("EUF_DIAG")) {
                auto exprOf = [&](EufTermId t) -> int {
                    for (auto& kv : sharedTermToEufTerm_) {
                        if (kv.second == t && sharedTermRegistry_) {
                            const auto* s = sharedTermRegistry_->get(kv.first);
                            if (s) return (int)s->coreExpr;
                        }
                    }
                    return -1;
                };
                auto kindOf = [&](int ex) -> int { return (ex >= 0 && coreIr_) ? (int)coreIr_->get((ExprId)ex).kind : -99; };
                int ea = exprOf(d.lhs), eb = exprOf(d.rhs);
                std::cerr << "[EUF-DIAG] SHARED-DISEQ-conflict lhs=" << d.lhs << "(expr" << ea << ",k" << kindOf(ea) << ")"
                          << " rhs=" << d.rhs << "(expr" << eb << ",k" << kindOf(eb) << ")"
                          << " ok=" << er.ok << " chain=" << er.reasons.size() << " reasons=";
                for (auto l : er.reasons) std::cerr << (l.sign?"":"-") << l.var << " ";
                std::cerr << " diseqReason=" << (d.reason.sign?"":"-") << d.reason.var << "\n";
            }
            if (er.ok) {
                er.reasons.push_back(d.reason);
#ifdef XOLVER_ENABLE_PROOFS
                pushEufTransitivityCert(er.reasons);
#endif
                return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
            }
            auto reasons = allActiveReasons();
            reasons.push_back(d.reason);
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
        }
    }

#ifndef NDEBUG
    assert(mergeQueue_.empty());
    assert(egraph_.congruenceClosed());
#endif

    // L2 measurement (XOLVER_AX_R2D_DIAG): of the Row2-eligible reads
    // (select(arr,j) with a store(a,i,v) in arr's class, i≠j-not-same), how many
    // have i≠j KNOWN-disequal in the e-graph right now? Decides whether eager
    // Row2-merge-on-known-diseq will fire at these Standard checkpoints.
    static const bool r2dDiag = xolver::env::diag("XOLVER_AX_R2D_DIAG");
    if (r2dDiag && arrayMode_ && arrayReasoner_.active()) {
        auto repPairKey = [](EClassId a, EClassId b) -> uint64_t {
            uint32_t lo = a < b ? a : b, hi = a < b ? b : a;
            return (static_cast<uint64_t>(lo) << 32) | hi;
        };
        std::unordered_set<uint64_t> knownDiseq;
        for (const auto& d : disequalities_)
            knownDiseq.insert(repPairKey(egraph_.rep(d.lhs), egraph_.rep(d.rhs)));
        for (const auto& d : sharedDisequalities_)
            knownDiseq.insert(repPairKey(egraph_.rep(d.lhs), egraph_.rep(d.rhs)));
        size_t eligible = 0, known = 0;
        for (EufTermId sel : arrayReasoner_.selectTerms()) {
            const auto& sn = termManager_.node(sel);
            if (sn.args.size() != 2) continue;
            EufTermId jTerm = sn.args[1];
            for (EufTermId m : egraph_.classMembers(egraph_.rep(sn.args[0]))) {
                if (!arrayReasoner_.isStore(m)) continue;
                const auto& mn = termManager_.node(m);
                if (mn.args.size() != 3) continue;
                EufTermId iTerm = mn.args[1];
                if (egraph_.same(iTerm, jTerm)) continue;
                ++eligible;
                if (knownDiseq.count(repPairKey(egraph_.rep(iTerm), egraph_.rep(jTerm))))
                    ++known;
            }
        }
        std::fprintf(stderr,
            "[R2D] effort=%d diseqs=%zu+%zu eligible=%zu knownDiseq=%zu\n",
            (int)effort, disequalities_.size(), sharedDisequalities_.size(),
            eligible, known);
        std::fflush(stderr);
    }

    // Datatype clash / acyclicity conflicts. Sound UNSAT detection against the
    // now-congruence-closed egraph; safe at any effort (a hard contradiction).
    if (dtMode_) {
        ensureDtContext();
        if (dtReasoner_.active()) {
            if (auto conflict = dtReasoner_.checkConflict()) {
                return TheoryCheckResult::mkConflict(TheoryConflict{std::move(*conflict)});
            }
        }
    }

    // L13: relevancy-bounded Row2 case-split at STANDARD effort
    // (XOLVER_AX_ROW2_SPLIT). The Row2 lemma (i=j ∨ readEq) is a THEORY TAUTOLOGY
    // (the array axiom), so emitting it on a partial assignment is SOUND. Reuses
    // instantiateLemma with a SEPARATE dedup set (row2SplitDone_) so it does NOT
    // mark row2Done_ and starve the Full-effort path (the ax_007 regression). The
    // lemmas are tagged ArraySplit; the propagator marks their atoms dynamically
    // relevant so cb_decide DECIDES i=j (try → refute via the whole formula →
    // i≠j → readEq forced → chain advances). Buffered for the entailment channel
    // (cb_propagate drops Standard-effort Lemma results). z3's lazy split, made
    // tractable by the lazy select bound + made effective by dynamic relevancy.
    // Default-ON: the Row2 case-split is a sound array TAUTOLOGY (completeness, not
    // a heuristic), so it is on by default; XOLVER_AX_ROW2_SPLIT=0 is a kill-switch.
    static const bool row2Split = [] {
        return xolver::env::flag("XOLVER_AX_ROW2_SPLIT", true);
    }();
    // Scoped to COMBINATION (sharedTermRegistry_ != null): generating the split
    // INTERNS new select terms into the e-graph, which perturbs the pure-QF_AX
    // Full-effort sat-gate (ax_007 unsat→unknown). cs_* / QF_ANIA is combination.
    if (arrayMode_ && row2Split && sharedTermRegistry_ && effort != TheoryEffort::Full) {
        ensureArrayContext();
        if (arrayReasoner_.active()) {
            auto diseqs = activeArrayDiseqs();
            const int kMaxSplitPerCheck = 64;
            for (int n = 0; n < kMaxSplitPerCheck; ++n) {
                auto lemma = arrayReasoner_.instantiateLemma(diseqs, &row2SplitDone_);
                if (!lemma || lemma->empty()) break;  // no more eligible
                TheoryLemma tl;
                tl.lits = std::move(*lemma);
                tl.kind = LemmaKind::ArraySplit;
                if (lemmaDb.contains(tl)) continue;
                row2SplitLemmas_.push_back(std::move(tl));
            }
            if (std::getenv("XOLVER_AX_R2D_DIAG") && !row2SplitLemmas_.empty()) {
                static size_t g_split = 0; g_split += row2SplitLemmas_.size();
                std::fprintf(stderr, "[R2-SPLIT] this=%zu cum=%zu\n",
                             row2SplitLemmas_.size(), g_split);
                std::fflush(stderr);
            }
        }
    }

    // Array Row2/Extensionality lemmas — emitted only at Full effort (complete
    // SAT model), so the case split is over a stable assignment. The lemma
    // literals are observed dynamic equality atoms; returning Lemma lets the
    // SAT solver branch on them and re-enter check().
    if (arrayMode_ && effort == TheoryEffort::Full) {
        ensureArrayContext();
        if (arrayReasoner_.active()) {
            auto diseqs = activeArrayDiseqs();
            auto lemma = arrayReasoner_.instantiateLemma(diseqs);
            if (lemma && !lemma->empty()) {
                TheoryLemma tl;
                tl.lits = std::move(*lemma);
                // Only emit if genuinely new; otherwise the same lemma would
                // be regenerated forever (the dedup caches already gate this,
                // but guard against a re-derivation across solver instances).
                if (!lemmaDb.contains(tl)) {
                    return TheoryCheckResult::mkLemma(std::move(tl));
                }
            }
        }
    }

    // #85 model-driven array refinement: the normal lazy lemma path above has
    // EXHAUSTED (row2Done_ saturated), but the candidate model may still VIOLATE a
    // Row2 axiom instance (the QF_AX storeinv multi-store residual: select(s,k)
    // and select(a,k) are left unmerged though k≠i). Re-scan with a FRESH dedup +
    // onlyViolated so we surface exactly the missed instance, and re-assert it as a
    // lemma to force the SAT solver off this array-inconsistent model. Bounded by
    // refineBudget_ (then accept; arrayModelDefinitelyViolates floors → sound).
    if (arrayMode_ && arrayRefineEnabled_ && effort == TheoryEffort::Full &&
        arrayRefineCount_ < arrayRefineBudget_) {
        ensureArrayContext();
        if (arrayReasoner_.active()) {
            auto diseqs = activeArrayDiseqs();
            std::unordered_set<uint64_t> freshDedup;
            auto lemma = arrayReasoner_.instantiateLemma(diseqs, &freshDedup, /*onlyViolated=*/true);
            if (lemma && !lemma->empty()) {
                ++arrayRefineCount_;
                TheoryLemma tl;
                tl.lits = std::move(*lemma);
                if (xolver::env::diag("XOLVER_AX_REFINE_DIAG"))
                    std::fprintf(stderr, "[REFINE] #%zu re-assert violated Row2 lits=%zu\n",
                                 arrayRefineCount_, tl.lits.size());
                return TheoryCheckResult::mkLemma(std::move(tl));
            }
        }
    }

    // Datatype injectivity / guarded-projection / exhaustiveness-split /
    // reconstruction lemmas (full effort). These propagate implied field
    // equalities, force a constructor choice for an observed class, or rebuild a
    // term from a decided tester — feeding back through the SAT core and
    // surfacing clash/diseq conflicts (e.g. finite cardinality).
    if (dtMode_ && effort == TheoryEffort::Full) {
        ensureDtContext();
        if (dtReasoner_.active()) {
            auto lemma = dtReasoner_.instantiateLemma();
            if (lemma && !lemma->empty()) {
                TheoryLemma tl;
                tl.lits = std::move(*lemma);
                if (!lemmaDb.contains(tl)) {
                    return TheoryCheckResult::mkLemma(std::move(tl));
                }
            }
        }
    }

    // Datatype completeness gate (the authoritative DT sat gate — satComplete is
    // not consulted on the single-theory path). A sat is sound only when every
    // OBSERVED datatype class (selector-read / decided-tester / finite-sort) has
    // a determined constructor, i.e. the DT structure is a concrete ground-term
    // model. Otherwise return Unknown: the propagator turns a Full-effort Unknown
    // into a sound `unknown` verdict rather than an unvalidated sat.
    if (dtMode_ && effort == TheoryEffort::Full) {
        ensureDtContext();
        if (dtReasoner_.active() && !dtReasoner_.modelFullyDetermined()) {
            return TheoryCheckResult::unknown(
                "dt: model not fully determined (observed datatype class has no constructor)");
        }
        // DT model re-validator: evaluate every original assertion under the
        // live e-graph. Catches false-SATs where modelFullyDetermined accepts
        // (every observed class has SOME ctor) but a deep BMC encoding
        // (ITE-chain over testers/selectors) is actually violated. SMT-LIB-
        // strict semantics: selector-on-wrong-ctor is Indeterminate, not
        // Violated — never over-rejects sat cases like `(head nil) = red`.
        // Default ON; XOLVER_DT_VALIDATE_OFF=1 disables (A/B escape).
        static const bool dtValidateOff =
            xolver::env::diag("XOLVER_DT_VALIDATE_OFF");
        if (!dtValidateOff && dtReasoner_.active() && coreIr_ &&
            originalAssertionsForDtValidate_ &&
            !originalAssertionsForDtValidate_->empty()) {
            DtModelValidator v(*coreIr_, termManager_, egraph_, coreIr_->datatypes());
            // Strict mode: floor on Indeterminate too. Master 5min batch
            // surfaced 43 false-SATs the lenient default missed (the e-graph
            // arrived at a sat verdict without enough constructor witnesses
            // for structural eval to ground out). Sound but may over-floor
            // true-sat opaque-DT cases. See validator header.
            static const bool dtValidatorStrict =
                xolver::env::diag("XOLVER_DT_VALIDATOR_STRICT");
            v.setStrictMode(dtValidatorStrict);
            auto verdict = v.validate(*originalAssertionsForDtValidate_);
            if (xolver::env::diag("XOLVER_DT_VALIDATE_DIAG")) {
                std::cerr << "[DT-VAL] assertions=" << originalAssertionsForDtValidate_->size()
                          << " verdict=" << (verdict == DtModelValidator::Verdict::Satisfied ? "Sat"
                                          : verdict == DtModelValidator::Verdict::Violated ? "Violated"
                                          : "Indeterminate") << "\n";
            }
            if (verdict == DtModelValidator::Verdict::Violated) {
                return TheoryCheckResult::unknown(
                    "dt: candidate model violates an original assertion "
                    "(DtModelValidator re-evaluation Violated; sound floor)");
            }
        }
    }

    // Capture the array/scalar model NOW, while the egraph reflects this
    // satisfying assignment. After solve() returns, the egraph is rolled back
    // and select/bridge merges are lost, so getModel() reads this snapshot.
    // Only at Full effort (a complete model check) is the state authoritative.
    if ((arrayMode_ || (ufModelEnabled_ && sharedTermRegistry_)) &&
        effort == TheoryEffort::Full) {
        modelSnapshot_ = buildModel();
    }

    return TheoryCheckResult::consistent();
}

} // namespace xolver
