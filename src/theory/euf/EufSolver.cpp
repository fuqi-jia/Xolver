#include <cstdlib>
#include "theory/euf/EufSolver.h"
#include "theory/core/DebugTrace.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "expr/ir.h"
#include <cassert>
#include <algorithm>
#include <functional>

namespace zolver {

EufSolver::EufSolver() : egraph_(termManager_) {
    initializeBoolConstants();
}

void EufSolver::push() {
    scopeLimits_.push_back(trail_.size());
    scopeSnapshots_.push_back(egraph_.snapshot());
}

void EufSolver::pop(uint32_t n) {
    while (n-- && !scopeLimits_.empty()) {
        size_t limit = scopeLimits_.back();
        EGraphSnapshot snap = scopeSnapshots_.back();

        trail_.resize(limit);

        // remove disequalities whose assignment was popped
        auto dit = std::remove_if(disequalities_.begin(), disequalities_.end(),
            [limit](const auto& d) { return d.trailIndex >= limit; });
        disequalities_.erase(dit, disequalities_.end());

        mergeQueue_.clear();

        egraph_.rollback(snap);

        // Reset bool marks: recompute from current egraph roots
        for (auto& info : classInfo_) {
            info.boolMark = BoolConstMark::None;
        }
        if (trueTerm_ != NullEufTerm) {
            classInfo(egraph_.rep(trueTerm_)).boolMark = BoolConstMark::True;
        }
        if (falseTerm_ != NullEufTerm) {
            classInfo(egraph_.rep(falseTerm_)).boolMark = BoolConstMark::False;
        }

        pendingConflict_.reset();
        pendingUnknown_ = false;

        // also clean up levelSnapshots that are now past current trail
        while (!levelSnapshots_.empty() && levelSnapshots_.back().trailSizeBeforeLevel >= limit) {
            levelSnapshots_.pop_back();
        }

        scopeLimits_.pop_back();
        scopeSnapshots_.pop_back();
    }
}

void EufSolver::reset() {
    modelSnapshot_.reset();
    trail_.clear();
    scopeLimits_.clear();
    scopeSnapshots_.clear();
    levelSnapshots_.clear();
    disequalities_.clear();
    pendingConflict_.reset();
    pendingUnknown_ = false;
    termManager_.clear();
    egraph_.clear();
    sharedTermToEufTerm_.clear();
    sharedDisequalities_.clear();

    classInfo_.clear();
    mergeQueue_.clear();
    trueTerm_ = NullEufTerm;
    falseTerm_ = NullEufTerm;

    arrayReasoner_.reset();

    initializeBoolConstants();
}

void EufSolver::ensureArrayContext() {
    if (!arrayMode_ || !coreIr_) return;
    if (!arrayReasoner_.active()) {
        arrayReasoner_.setContext(&termManager_, &egraph_, coreIr_, arrayRegistry_);
        // In combination logics the indices/elements are shared arith terms;
        // hand the reasoner the SharedTermRegistry so Row2 builds (i=j) as a
        // shared-equality atom. Null in pure QF_AX.
        arrayReasoner_.setSharedTermRegistry(sharedTermRegistry_);
    }
}

std::vector<ArrayReasoner::ArrayDiseq> EufSolver::activeArrayDiseqs() const {
    std::vector<ArrayReasoner::ArrayDiseq> out;
    if (!arrayMode_ || !coreIr_) return out;
    auto isArraySort = [&](EufTermId t) {
        if (t == NullEufTerm) return false;
        return coreIr_->arraySortParams(termManager_.node(t).sort).has_value();
    };
    for (const auto& d : disequalities_) {
        if (isArraySort(d.lhs) && isArraySort(d.rhs)) {
            out.push_back({d.lhs, d.rhs});
        }
    }
    return out;
}

void EufSolver::ensureSnapshotForLevel(int level) {
    if (!levelSnapshots_.empty() && levelSnapshots_.back().level > level) {
        if (std::getenv("EUF_DIAG")) {
            std::cerr << "[EUF_ASSERT_FAIL] ensureSnapshotForLevel level=" << level
                      << " backLevel=" << levelSnapshots_.back().level
                      << " snapCount=" << levelSnapshots_.size() << "\n";
        }
    }
    assert(levelSnapshots_.empty() || levelSnapshots_.back().level <= level);

    if (levelSnapshots_.empty() || levelSnapshots_.back().level < level) {
        levelSnapshots_.push_back({
            level,
            trail_.size(),
            egraph_.snapshot(),
            mergeQueue_.size()
        });
    }
}

void EufSolver::backtrackToLevel(int target) {
    currentLevel_ = target;

    // Find the rightmost snapshot with level <= target
    const LevelSnapshot* targetSnap = nullptr;
    for (auto it = levelSnapshots_.rbegin(); it != levelSnapshots_.rend(); ++it) {
        if (it->level <= target) {
            targetSnap = &*it;
            break;
        }
    }

    // Pop all snapshots above target
    while (!levelSnapshots_.empty() && levelSnapshots_.back().level > target) {
        levelSnapshots_.pop_back();
    }

    if (targetSnap) {
        trail_.resize(targetSnap->trailSizeBeforeLevel);

        auto dit = std::remove_if(disequalities_.begin(), disequalities_.end(),
            [targetSnap](const auto& d) { return d.trailIndex >= targetSnap->trailSizeBeforeLevel; });
        disequalities_.erase(dit, disequalities_.end());

        mergeQueue_.resize(targetSnap->mergeQueueSize);

        egraph_.rollback(targetSnap->egraphSnapshotBeforeLevel);
    } else {
        // No snapshot at or below target - clear everything
        trail_.clear();
        disequalities_.clear();
        mergeQueue_.clear();
        egraph_.rollback({0, 0, 0, 0, 0, 0});
    }

    auto sdIt = std::remove_if(sharedDisequalities_.begin(), sharedDisequalities_.end(),
        [target](const auto& d) { return d.level > target; });
    sharedDisequalities_.erase(sdIt, sharedDisequalities_.end());

    // clean scope stack if needed
    while (!scopeLimits_.empty() && scopeLimits_.back() > trail_.size()) {
        scopeLimits_.pop_back();
        scopeSnapshots_.pop_back();
    }

    // Reset bool marks: recompute from current egraph roots
    for (auto& info : classInfo_) {
        info.boolMark = BoolConstMark::None;
    }
    if (trueTerm_ != NullEufTerm) {
        classInfo(egraph_.rep(trueTerm_)).boolMark = BoolConstMark::True;
    }
    if (falseTerm_ != NullEufTerm) {
        classInfo(egraph_.rep(falseTerm_)).boolMark = BoolConstMark::False;
    }

    pendingConflict_.reset();
    pendingUnknown_ = false;
}

void EufSolver::initializeBoolConstants() {
    trueTerm_ = termManager_.internTrueConstant();
    falseTerm_ = termManager_.internFalseConstant();
    egraph_.setTrueTerm(trueTerm_);
    egraph_.setFalseTerm(falseTerm_);
    egraph_.ensureTermRegistered(trueTerm_, mergeQueue_);
    egraph_.ensureTermRegistered(falseTerm_, mergeQueue_);

    if (trueTerm_ != NullEufTerm) {
        classInfo(egraph_.rep(trueTerm_)).boolMark = BoolConstMark::True;
    }
    if (falseTerm_ != NullEufTerm) {
        classInfo(egraph_.rep(falseTerm_)).boolMark = BoolConstMark::False;
    }
}

EufSolver::EClassInfo& EufSolver::classInfo(EClassId id) {
    if (classInfo_.size() <= id) classInfo_.resize(id + 1);
    return classInfo_[id];
}

EufSolver::BoolConstMark EufSolver::mergeBoolMark(BoolConstMark a, BoolConstMark b) {
    if (a == BoolConstMark::Both || b == BoolConstMark::Both) return BoolConstMark::Both;
    if (a == BoolConstMark::None) return b;
    if (b == BoolConstMark::None) return a;
    if (a == b) return a;
    return BoolConstMark::Both;
}

std::vector<SatLit> EufSolver::allActiveReasons() const {
    std::vector<SatLit> reasons;
    reasons.reserve(trail_.size() + disequalities_.size() + sharedDisequalities_.size());
    for (const auto& e : trail_) {
        reasons.push_back(e.lit);
    }
    for (const auto& d : disequalities_) {
        reasons.push_back(d.reason);
    }
    for (const auto& d : sharedDisequalities_) {
        reasons.push_back(d.reason);
    }
    std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    reasons.erase(std::unique(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), reasons.end());
    return reasons;
}

void EufSolver::onEclassMerged(EClassId kept, EClassId killed) {
    auto& kInfo = classInfo(kept);
    auto& dInfo = classInfo(killed);

    BoolConstMark merged = mergeBoolMark(kInfo.boolMark, dInfo.boolMark);
    kInfo.boolMark = merged;
    dInfo.boolMark = BoolConstMark::None;

    // Both -> conflict
    if (merged == BoolConstMark::Both) {
        auto er = egraph_.explainEquality(trueTerm_, falseTerm_);
        if (std::getenv("EUF_DIAG")) {
            std::cerr << "[EUF-DIAG] BOOL-BOTH kept=" << kept << " killed=" << killed
                      << " kMark=" << (int)kInfo.boolMark << " dMark=" << (int)dInfo.boolMark
                      << " explainTF.ok=" << er.ok << " chain=" << er.reasons.size()
                      << " trueRep=" << egraph_.rep(trueTerm_) << " falseRep=" << egraph_.rep(falseTerm_) << "\n";
        }
        if (er.ok && egraph_.same(trueTerm_, falseTerm_)) {
            pendingConflict_ = TheoryConflict{std::move(er.reasons)};
        } else {
            // SOUNDNESS: a Both boolMark means this class is tagged as
            // containing a term equal to `true` AND a term equal to `false`.
            // But the mark is propagated by class-merge bookkeeping
            // (mergeBoolMark) which, in rare orderings driven by array
            // Row1/Row2 reasoning over compound/bridge indices, can tag a
            // class Both even though the genuine `true` and `false` constant
            // terms are NOT in the same egraph class (here trueRep != falseRep,
            // so explainEquality(true,false) correctly reports !ok — there is
            // no real true == false derivation). Emitting allActiveReasons() as
            // a conflict in that case is UNSOUND: it asserts that the current,
            // perfectly satisfiable assignment is contradictory, producing a
            // spurious UNSAT (observed as an intermittent false-unsat on
            // QF_A(UF)L(I/R)A formulas with purified compound array indices).
            //
            // Only emit a conflict when true and false are genuinely merged
            // (the `ok` branch above, which carries a real reason chain). When
            // they are not, there is no sound conflict to report; fall through
            // without setting pendingConflict_. Congruence continues normally
            // and the model is validated by the exact kernel before any SAT is
            // returned, so soundness is preserved. At worst this is incomplete
            // (the genuine conflict, if any, is found via another path or the
            // result is Unknown) — never a wrong verdict.
            NO_DBG << "[EUF] BOOL-BOTH mark without a real true==false merge "
                      "(trueRep != falseRep); suppressing unsound fallback conflict\n";
        }

    }
}

// ---------------------------------------------------------------------------
// assertLit
// ---------------------------------------------------------------------------

void EufSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) {
    if (!std::holds_alternative<EufAtomPayload>(atom.payload)) return;
    const auto& payload = std::get<EufAtomPayload>(atom.payload);

    ensureSnapshotForLevel(level);

    // Lazily intern true/false constants
    EufTermId trueTerm = termManager_.internTrueConstant();
    EufTermId falseTerm = termManager_.internFalseConstant();
    egraph_.setTrueTerm(trueTerm);
    egraph_.setFalseTerm(falseTerm);
    egraph_.ensureTermRegistered(trueTerm, mergeQueue_);
    egraph_.ensureTermRegistered(falseTerm, mergeQueue_);

    // Update our cached true/false roots if they changed
    if (trueTerm_ == NullEufTerm) {
        trueTerm_ = trueTerm;
        classInfo(egraph_.rep(trueTerm_)).boolMark = BoolConstMark::True;
    }
    if (falseTerm_ == NullEufTerm) {
        falseTerm_ = falseTerm;
        classInfo(egraph_.rep(falseTerm_)).boolMark = BoolConstMark::False;
    }

    // Intern lhs/rhs (monotonic)
    EufTermId lhs = termManager_.intern(payload.lhs, *coreIr_);
    EufTermId rhs = termManager_.intern(payload.rhs, *coreIr_);
    if (lhs == NullEufTerm || rhs == NullEufTerm) {
        pendingUnknown_ = true;
        return;
    }

    egraph_.ensureTermRegistered(lhs, mergeQueue_);
    egraph_.ensureTermRegistered(rhs, mergeQueue_);

    if (payload.kind == EufAtomKind::BoolTermAsFormula) {
        EufTermId target = value ? trueTerm : falseTerm;
        trail_.push_back({level, reason, atom, value});
        MergeReason mr;
        mr.kind = MergeReasonKind::AssertedEquality;
        mr.lit = reason;
        mergeQueue_.push_back({lhs, target, mr});
        return;
    }

    bool isEq = false;
    if (payload.rel == Relation::Eq) {
        isEq = value;
    } else if (payload.rel == Relation::Neq) {
        isEq = !value;
    } else {
        return;
    }

    size_t trailIdx = trail_.size();
    trail_.push_back({level, reason, atom, value});

    if (isEq) {
        MergeReason mr;
        mr.kind = MergeReasonKind::AssertedEquality;
        mr.lit = reason;
        mergeQueue_.push_back({lhs, rhs, mr});
    } else {
        disequalities_.push_back({lhs, rhs, reason, level, trailIdx});
    }
}

// ---------------------------------------------------------------------------
// check — 唯一 saturation loop
// ---------------------------------------------------------------------------

TheoryCheckResult EufSolver::check(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    if (pendingUnknown_) {
        return TheoryCheckResult::unknown();
    }
    if (pendingConflict_) {
        return TheoryCheckResult::mkConflict(*pendingConflict_);
    }

    // Array Row1/Const eager merges (tautological; re-enqueued after backtrack
    // since the egraph rolls these merges back). Must happen before the
    // saturation loop so the consequences propagate via congruence.
    if (arrayMode_) {
        ensureArrayContext();
        if (arrayReasoner_.active()) {
            arrayReasoner_.enqueueEagerMerges(mergeQueue_);
        }
    }

    // Register signatures for all newly interned terms before entering the
    // saturation loop.  This ensures late-interned terms (e.g. f(a) after a=b
    // has already been merged) are visible to congruence detection.
    egraph_.registerPendingSignatures(mergeQueue_);

    // 唯一 saturation loop：drain SAT decisions + congruence
    while (!mergeQueue_.empty()) {
        auto req = mergeQueue_.back();
        mergeQueue_.pop_back();
        if (egraph_.same(req.a, req.b)) continue;

        // sort check
        const auto& na = termManager_.node(req.a);
        const auto& nb = termManager_.node(req.b);
        if (na.sort != nb.sort && na.sort != NullSort && nb.sort != NullSort) {
            pendingUnknown_ = true;
            return TheoryCheckResult::unknown();
        }

        auto mr = egraph_.merge(req.a, req.b, req.reason, mergeQueue_);
        if (!mr.merged) continue;

        // Evaluate builtin constants in affected parent terms
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
            tryEvaluateBuiltin(p);
        }

        // ITE metadata：只 enqueue，不递归 merge
        onEclassMerged(mr.kept, mr.killed);
        if (pendingConflict_) {
            return TheoryCheckResult::mkConflict(*pendingConflict_);
        }
        // refreshCongruence is now handled inside merge()
    }

    // true/false conflict
    if (trueTerm_ != NullEufTerm && falseTerm_ != NullEufTerm &&
        egraph_.same(trueTerm_, falseTerm_)) {
        auto er = egraph_.explainEquality(trueTerm_, falseTerm_);
        if (std::getenv("EUF_DIAG")) {
            std::cerr << "[EUF-DIAG] TRUE-FALSE-conflict ok=" << er.ok
                      << " chain=" << er.reasons.size() << "\n";
        }
        if (er.ok) {
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
        }
        std::cerr << "[EUF_EXPLAIN_FAIL] true=false same=" << egraph_.same(trueTerm_, falseTerm_)
                  << " activeReasons=" << allActiveReasons().size() << "\n";
        return TheoryCheckResult::mkConflict(TheoryConflict{allActiveReasons()});
    }

    // disequality conflicts
    for (const auto& d : disequalities_) {
        if (egraph_.same(d.lhs, d.rhs)) {
            auto er = egraph_.explainEquality(d.lhs, d.rhs);
            if (std::getenv("EUF_DIAG")) {
                std::cerr << "[EUF-DIAG] diseq-conflict lhs=" << d.lhs << " rhs=" << d.rhs
                          << " ok=" << er.ok << " chain=" << er.reasons.size() << " reasons=";
                for (auto l : er.reasons) std::cerr << (l.sign?"":"-") << l.var << " ";
                std::cerr << " diseqReason=" << (d.reason.sign?"":"-") << d.reason.var << "\n";
            }
            if (er.ok) {
                er.reasons.push_back(d.reason);
                return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
            }
            std::cerr << "[EUF_EXPLAIN_FAIL] diseq lhs=" << d.lhs << " rhs=" << d.rhs
                      << " same=" << egraph_.same(d.lhs, d.rhs)
                      << " activeReasons=" << allActiveReasons().size() << "\n";
            auto reasons = allActiveReasons();
            reasons.push_back(d.reason);
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
        }
    }

    // shared disequality conflicts
    for (const auto& d : sharedDisequalities_) {
        if (egraph_.same(d.lhs, d.rhs)) {
            auto er = egraph_.explainEquality(d.lhs, d.rhs);
            if (std::getenv("EUF_DIAG")) {
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

    // Capture the array/scalar model NOW, while the egraph reflects this
    // satisfying assignment. After solve() returns, the egraph is rolled back
    // and select/bridge merges are lost, so getModel() reads this snapshot.
    // Only at Full effort (a complete model check) is the state authoritative.
    if (arrayMode_ && effort == TheoryEffort::Full) {
        modelSnapshot_ = buildModel();
    }

    return TheoryCheckResult::consistent();
}

// ---------------------------------------------------------------------------
// Nelson-Oppen combination hooks
// ---------------------------------------------------------------------------

EufTermId EufSolver::internSharedConstant(SharedTermId s) {
    auto it = sharedTermToEufTerm_.find(s);
    if (it != sharedTermToEufTerm_.end()) {
        return it->second;
    }

    if (!sharedTermRegistry_ || !coreIr_) return NullEufTerm;
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return NullEufTerm;

    EufTermId t = termManager_.intern(st->coreExpr, const_cast<CoreIr&>(*coreIr_));
    if (t != NullEufTerm) {
        sharedTermToEufTerm_[s] = t;
        egraph_.ensureTermRegistered(t, mergeQueue_);
    }
    return t;
}

EufTermId EufSolver::internEufExpr(ExprId eid) {
    if (!coreIr_) return NullEufTerm;
    EufTermId t = termManager_.intern(eid, const_cast<CoreIr&>(*coreIr_));
    if (t != NullEufTerm) {
        egraph_.ensureTermRegistered(t, mergeQueue_);
    }
    return t;
}

TheoryCheckResult EufSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    ensureSnapshotForLevel(level);

    EufTermId ta = internSharedConstant(a);
    EufTermId tb = internSharedConstant(b);
    if (ta == NullEufTerm || tb == NullEufTerm) {
        return TheoryCheckResult::unknown();
    }

    MergeReason mr;
    mr.kind = MergeReasonKind::AssertedEquality;
    mr.lit = reason;
    mergeQueue_.push_back({ta, tb, mr});
    return TheoryCheckResult::consistent();
}

TheoryCheckResult EufSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    ensureSnapshotForLevel(level);

    EufTermId ta = internSharedConstant(a);
    EufTermId tb = internSharedConstant(b);
    if (ta == NullEufTerm || tb == NullEufTerm) {
        return TheoryCheckResult::unknown();
    }

    if (egraph_.same(ta, tb)) {
        auto er = egraph_.explainEquality(ta, tb);
        if (std::getenv("EUF_DIAG")) {
            const auto* sa = sharedTermRegistry_ ? sharedTermRegistry_->get(a) : nullptr;
            const auto* sb = sharedTermRegistry_ ? sharedTermRegistry_->get(b) : nullptr;
            auto dump = [&](const char* tag, auto s) {
                std::cerr << " " << tag << "{";
                if (s && coreIr_) {
                    const auto& e = coreIr_->get(s->coreExpr);
                    std::cerr << "expr=" << (int)s->coreExpr << " kind=" << (int)e.kind;
                    if (auto* iv = std::get_if<int64_t>(&e.payload.value)) std::cerr << " int=" << *iv;
                    else if (auto* sv = std::get_if<std::string>(&e.payload.value)) std::cerr << " sym=" << *sv;
                    std::cerr << " nch=" << e.children.size();
                }
                std::cerr << "}";
            };
            std::cerr << "[EUF-DIAG] IFACE-DISEQ-IMMEDIATE sharedA=" << a << " sharedB=" << b
                      << " ta=" << ta << " tb=" << tb << " sameSharedId=" << (a == b);
            dump("A", sa); dump("B", sb);
            std::cerr << " ok=" << er.ok << " chain=" << er.reasons.size() << "\n";
        }
        if (er.ok) {
            er.reasons.push_back(reason);
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
        }
        auto reasons = allActiveReasons();
        reasons.push_back(reason);
        return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
    }

    sharedDisequalities_.push_back({ta, tb, reason, level, trail_.size()});
    return TheoryCheckResult::consistent();
}

bool EufSolver::areSharedTermsMerged(SharedTermId a, SharedTermId b) const {
    if (a == b) return true;
    // Only consult terms that have ALREADY been interned as shared constants.
    // Interning is a mutating operation (registers signatures / enqueues
    // merges), so a const observer must not trigger it. If a shared scalar has
    // never been interned, it cannot be merged with anything on the EUF side
    // yet -> report not-merged (conservative).
    auto ia = sharedTermToEufTerm_.find(a);
    auto ib = sharedTermToEufTerm_.find(b);
    if (ia == sharedTermToEufTerm_.end() || ib == sharedTermToEufTerm_.end())
        return false;
    if (ia->second == NullEufTerm || ib->second == NullEufTerm) return false;
    return egraph_.same(ia->second, ib->second);
}

std::vector<TheorySolver::SharedEqualityPropagation>
EufSolver::getDeducedSharedEqualities() {
    std::vector<SharedEqualityPropagation> result;
    if (!sharedTermRegistry_) return result;

    const auto& allShared = sharedTermRegistry_->allSharedTerms();
    for (size_t i = 0; i < allShared.size(); ++i) {
        EufTermId ti = internSharedConstant(allShared[i]);
        if (ti == NullEufTerm) continue;
        for (size_t j = i + 1; j < allShared.size(); ++j) {
            EufTermId tj = internSharedConstant(allShared[j]);
            if (tj == NullEufTerm) continue;
            if (egraph_.same(ti, tj)) {
                auto er = egraph_.explainEquality(ti, tj);
                if (er.ok) {
                    result.push_back({allShared[i], allShared[j], std::move(er.reasons)});
                }
            }
        }
    }

    return result;
}

std::optional<TheorySolver::TheoryModel> EufSolver::getModel() const {
    // The array/scalar model must be read off the egraph WHILE it reflects the
    // satisfying assignment. By the time the Solver calls getModel() (after
    // solve() returns), the egraph has been rolled back, so select/bridge
    // merges no longer hold. We therefore return the snapshot captured at the
    // last consistent Full-effort check. Fall back to a live build only if no
    // snapshot exists (defensive — e.g. a non-array EUF problem).
    if (modelSnapshot_) return modelSnapshot_;
    return buildModel();
}

std::optional<TheorySolver::TheoryModel> EufSolver::buildModel() const {
    if (!arrayMode_ || !coreIr_) return std::nullopt;

    TheoryModel model;

    // Token for an eclass, in the ArithModelValidator's CANONICAL namespaced
    // form so the validator's asToken() and these tokens compare identically:
    //   numeric literal  -> "#n:<canonical-rational>"
    //   bool literal      -> "#b:1" / "#b:0"
    //   otherwise         -> opaque per-class marker "@e<rep>"
    // Index/element sorts may be uninterpreted; equality-by-token is exactly
    // the QF_AX semantics.
    auto classToken = [&](EufTermId t) -> std::string {
        if (t == NullEufTerm) return "@nil";
        EClassId rep = egraph_.rep(t);
        for (EufTermId m : egraph_.classMembers(rep)) {
            const auto& mn = termManager_.node(m);
            if (mn.origin == NullExpr) continue;
            if (mn.origin == TrueSentinelExpr || mn.origin == FalseSentinelExpr) continue;
            const auto& e = coreIr_->get(mn.origin);
            if (e.isConst()) {
                if (auto* i = std::get_if<int64_t>(&e.payload.value))
                    return "#n:" + mpq_class(*i).get_str();
                if (auto* b = std::get_if<bool>(&e.payload.value))
                    return std::string("#b:") + (*b ? "1" : "0");
                if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                    // Numeric literal stored as string (Int/Real const).
                    try { return "#n:" + mpq_class(*s).get_str(); } catch (...) {}
                    return *s;
                }
            }
        }
        return "@e" + std::to_string(rep);
    };

    // Group array variables by eclass so equal arrays share one interp.
    // Identify array variables in the CoreIr (Variable nodes with array sort).
    struct ArrBuild {
        std::string defaultVal;
        bool hasConstDefault = false;
        std::string indexSort, elemSort;
        // index-token -> value-token, plus the index-class rep used for dedup.
        std::vector<std::pair<std::string, std::string>> entries;
        std::unordered_set<EClassId> seenIdxClass;
    };
    std::unordered_map<EClassId, ArrBuild> byClass;

    auto sortName = [&](SortId s) -> std::string {
        auto sk = coreIr_->sortKind(s);
        if (sk == SortKind::Int) return "Int";
        if (sk == SortKind::Real) return "Real";
        if (sk == SortKind::Bool) return "Bool";
        return "U" + std::to_string(s);
    };

    // Collect every array variable EufTermId.
    std::vector<std::pair<std::string, EufTermId>> arrayVars;
    for (ExprId id = 0; id < static_cast<ExprId>(coreIr_->size()); ++id) {
        const auto& e = coreIr_->get(id);
        if (e.kind != Kind::Variable) continue;
        if (!coreIr_->arraySortParams(e.sort)) continue;
        if (!std::holds_alternative<std::string>(e.payload.value)) continue;
        // Intern is monotonic; the term should already exist if it was used.
        EufTermId t = const_cast<EufTermManager&>(termManager_)
                          .intern(id, const_cast<CoreIr&>(*coreIr_));
        if (t == NullEufTerm) continue;
        arrayVars.push_back({std::get<std::string>(e.payload.value), t});
    }
    if (arrayVars.empty()) return std::nullopt;

    // Seed an ArrBuild per array class, recording sorts + const default.
    for (const auto& [name, t] : arrayVars) {
        EClassId rep = egraph_.rep(t);
        auto& ab = byClass[rep];
        const auto& tn = termManager_.node(t);
        if (auto params = coreIr_->arraySortParams(tn.sort)) {
            ab.indexSort = sortName(params->first);
            ab.elemSort = sortName(params->second);
        }
        // const default if the class contains a const-array.
        if (!ab.hasConstDefault) {
            for (EufTermId m : egraph_.classMembers(rep)) {
                if (arrayReasoner_.isConstArray(m)) {
                    const auto& cn = termManager_.node(m);
                    if (cn.args.size() == 1) {
                        ab.defaultVal = classToken(cn.args[0]);
                        ab.hasConstDefault = true;
                    }
                    break;
                }
            }
        }
    }

    // Populate entries from select terms. select(arr,idx): the arr-class gets
    // an entry idx-token -> value-token where value = the select term's class.
    for (EufTermId sel : arrayReasoner_.selectTerms()) {
        const auto& sn = termManager_.node(sel);
        if (sn.args.size() != 2) continue;
        EClassId arrRep = egraph_.rep(sn.args[0]);
        auto it = byClass.find(arrRep);
        if (it == byClass.end()) continue;  // select on a non-variable class
        EClassId idxRep = egraph_.rep(sn.args[1]);
        if (!it->second.seenIdxClass.insert(idxRep).second) continue;
        it->second.entries.push_back({classToken(sn.args[1]), classToken(sel)});
    }

    // Assign a per-class default token when no const was found. Distinct
    // classes get distinct defaults so two unconstrained arrays differ at any
    // index not pinned by a shared read (defense; disequalities are also
    // witnessed by Ext read indices).
    for (auto& [rep, ab] : byClass) {
        if (!ab.hasConstDefault) {
            ab.defaultVal = "@def" + std::to_string(rep);
        }
    }

    // Emit one ArrayInterp per array variable (sharing the class build).
    for (const auto& [name, t] : arrayVars) {
        EClassId rep = egraph_.rep(t);
        auto it = byClass.find(rep);
        if (it == byClass.end()) continue;
        TheoryModel::ArrayInterp ai;
        ai.indexSort = it->second.indexSort;
        ai.elemSort = it->second.elemSort;
        ai.defaultVal = it->second.defaultVal;
        ai.entries = it->second.entries;
        model.arrayInterps[name] = std::move(ai);
    }

    if (model.arrayInterps.empty()) return std::nullopt;

    // Scalar token assignments for every non-array, non-bool variable that the
    // egraph knows about (index/element vars). The validator needs these to
    // evaluate select/store; tokens are the same class tokens used in the
    // array interps, so they stay consistent. Bool vars stay in `assignments`
    // as "true"/"false"; numeric literals stay numeric.
    for (ExprId id = 0; id < static_cast<ExprId>(coreIr_->size()); ++id) {
        const auto& e = coreIr_->get(id);
        if (e.kind != Kind::Variable) continue;
        if (coreIr_->arraySortParams(e.sort)) continue;  // arrays handled above
        if (!std::holds_alternative<std::string>(e.payload.value)) continue;
        const std::string& name = std::get<std::string>(e.payload.value);
        if (model.assignments.count(name)) continue;
        // Only emit if the variable was actually interned (used in a term).
        EufTermId t = const_cast<EufTermManager&>(termManager_)
                          .intern(id, const_cast<CoreIr&>(*coreIr_));
        if (t == NullEufTerm) continue;
        auto sk = coreIr_->sortKind(e.sort);
        if (sk == SortKind::Bool) {
            // Resolve against the true/false classes if forced; else default.
            if (trueTerm_ != NullEufTerm && egraph_.same(t, trueTerm_))
                model.assignments[name] = "true";
            else if (falseTerm_ != NullEufTerm && egraph_.same(t, falseTerm_))
                model.assignments[name] = "false";
            continue;
        }
        model.assignments[name] = classToken(t);
    }

    return model;
}

void EufSolver::tryEvaluateBuiltin(EufTermId t) {
    if (!coreIr_) return;
    const auto& node = termManager_.node(t);
    if (node.args.empty()) return;

    std::string symName = termManager_.symbolName(node.symbol);
    if (symName.empty() || symName[0] != '#') return;

    // Collect constant argument values from the equivalence class of each arg
    std::vector<mpq_class> values;
    values.reserve(node.args.size());
    for (EufTermId arg : node.args) {
        EClassId cid = egraph_.rep(arg);
        bool found = false;
        mpq_class val;
        for (EufTermId member : egraph_.classMembers(cid)) {
            const auto& mnode = termManager_.node(member);
            if (mnode.origin == NullExpr) continue;
            const auto& expr = coreIr_->get(mnode.origin);
            if (!expr.isConst()) continue;
            if (auto* i = std::get_if<int64_t>(&expr.payload.value)) {
                val = mpq_class(*i);
                found = true;
                break;
            } else if (auto* s = std::get_if<std::string>(&expr.payload.value)) {
                try {
                    val = mpq_class(*s);
                    found = true;
                    break;
                } catch (...) {
                    continue;
                }
            }
        }
        if (!found) return;
        values.push_back(val);
    }

    mpq_class result;
    bool ok = false;
    if (symName == "#builtin.Add") {
        if (values.size() != 2) return;
        result = values[0] + values[1];
        ok = true;
    } else if (symName == "#builtin.Sub") {
        if (values.size() != 2) return;
        result = values[0] - values[1];
        ok = true;
    } else if (symName == "#builtin.Neg") {
        if (values.size() != 1) return;
        result = -values[0];
        ok = true;
    } else if (symName == "#builtin.Mul") {
        if (values.size() != 2) return;
        result = values[0] * values[1];
        ok = true;
    } else if (symName == "#builtin.Div") {
        if (values.size() != 2) return;
        if (values[1] == 0) return;
        result = values[0] / values[1];
        ok = true;
    } else if (symName == "#builtin.Mod") {
        if (values.size() != 2) return;
        if (values[1] == 0) return;
        // mpq_class doesn't have mod; use integer mod if both are integers
        if (values[0].get_den() == 1 && values[1].get_den() == 1) {
            mpz_class r = values[0].get_num() % values[1].get_num();
            result = mpq_class(r);
            ok = true;
        }
    } else if (symName == "#builtin.Abs") {
        if (values.size() != 1) return;
        result = abs(values[0]);
        ok = true;
    }

    if (!ok) return;

    std::string resultStr = result.get_str();
    EufTermId constTerm = termManager_.internConstant(resultStr, node.sort);
    if (constTerm != NullEufTerm && !egraph_.same(t, constTerm)) {
        MergeReason mr;
        mr.kind = MergeReasonKind::BuiltinEval;
        mr.lit = SatLit();
        mergeQueue_.push_back({t, constTerm, mr});
    }
}

} // namespace zolver
