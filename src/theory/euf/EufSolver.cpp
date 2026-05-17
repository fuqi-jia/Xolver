#include "theory/euf/EufSolver.h"
#include "theory/DebugTrace.h"
#include <iostream>
#include "theory/TheoryLemmaDatabase.h"
#include <cassert>
#include <algorithm>
#include <iostream>

namespace nlcolver {

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

        // rollback ITE metadata before egraph
        while (!iteOccMoveTrail_.empty()) {
            auto t = iteOccMoveTrail_.back();
            iteOccMoveTrail_.pop_back();

            auto& kInfo = classInfo(t.kept);
            auto& dInfo = classInfo(t.killed);

            auto moveTailBack = [](auto& kept, auto& killed,
                                   size_t keptOldSize, size_t /*killedOldSize*/,
                                   size_t movedCount) {
                assert(kept.size() == keptOldSize + movedCount);
                for (size_t i = 0; i < movedCount; ++i) {
                    killed.push_back(kept[keptOldSize + i]);
                }
                kept.resize(keptOldSize);
            };

            moveTailBack(kInfo.condUses, dInfo.condUses,
                         t.keptCondOldSize, t.killedCondOldSize, t.movedCondCount);
            moveTailBack(kInfo.thenUses, dInfo.thenUses,
                         t.keptThenOldSize, t.killedThenOldSize, t.movedThenCount);
            moveTailBack(kInfo.elseUses, dInfo.elseUses,
                         t.keptElseOldSize, t.killedElseOldSize, t.movedElseCount);

            kInfo.boolMark = t.keptOldMark;
            dInfo.boolMark = t.killedOldMark;
        }
        mergeQueue_.clear();

        egraph_.rollback(snap);
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

    iteRecords_.clear();
    iteOfResult_.clear();
    classInfo_.clear();
    iteOccMoveTrail_.clear();
    mergeQueue_.clear();
    nextTermToScan_ = 0;
    trueTerm_ = NullEufTerm;
    falseTerm_ = NullEufTerm;

    initializeBoolConstants();
}

void EufSolver::ensureSnapshotForLevel(int level) {
    assert(levelSnapshots_.empty() || levelSnapshots_.back().level <= level);

    if (levelSnapshots_.empty() || levelSnapshots_.back().level < level) {
        levelSnapshots_.push_back({
            level,
            trail_.size(),
            egraph_.snapshot(),
            {iteOccMoveTrail_.size(), mergeQueue_.size(), nextTermToScan_}
        });
    }
}

void EufSolver::backtrackToLevel(int target) {
    currentLevel_ = target;

    while (!levelSnapshots_.empty() && levelSnapshots_.back().level > target) {
        auto snap = levelSnapshots_.back();
        levelSnapshots_.pop_back();

        trail_.resize(snap.trailSizeBeforeLevel);

        auto dit = std::remove_if(disequalities_.begin(), disequalities_.end(),
            [snap](const auto& d) { return d.trailIndex >= snap.trailSizeBeforeLevel; });
        disequalities_.erase(dit, disequalities_.end());

        // rollback ITE metadata before egraph
        mergeQueue_.resize(snap.iteSnapshot.mergeQueueSize);

        while (iteOccMoveTrail_.size() > snap.iteSnapshot.occMoveTrailSize) {
            auto t = iteOccMoveTrail_.back();
            iteOccMoveTrail_.pop_back();

            auto& kInfo = classInfo(t.kept);
            auto& dInfo = classInfo(t.killed);

            auto moveTailBack = [](auto& kept, auto& killed,
                                   size_t keptOldSize, size_t /*killedOldSize*/,
                                   size_t movedCount) {
                assert(kept.size() == keptOldSize + movedCount);
                for (size_t i = 0; i < movedCount; ++i) {
                    killed.push_back(kept[keptOldSize + i]);
                }
                kept.resize(keptOldSize);
            };

            moveTailBack(kInfo.condUses, dInfo.condUses,
                         t.keptCondOldSize, t.killedCondOldSize, t.movedCondCount);
            moveTailBack(kInfo.thenUses, dInfo.thenUses,
                         t.keptThenOldSize, t.killedThenOldSize, t.movedThenCount);
            moveTailBack(kInfo.elseUses, dInfo.elseUses,
                         t.keptElseOldSize, t.killedElseOldSize, t.movedElseCount);

            kInfo.boolMark = t.keptOldMark;
            dInfo.boolMark = t.killedOldMark;
        }

        egraph_.rollback(snap.egraphSnapshotBeforeLevel);
    }

    auto sdIt = std::remove_if(sharedDisequalities_.begin(), sharedDisequalities_.end(),
        [target](const auto& d) { return d.level > target; });
    sharedDisequalities_.erase(sdIt, sharedDisequalities_.end());

    // clean scope stack if needed
    while (!scopeLimits_.empty() && scopeLimits_.back() > trail_.size()) {
        scopeLimits_.pop_back();
        scopeSnapshots_.pop_back();
    }

    pendingConflict_.reset();
    pendingUnknown_ = false;
}

// ---------------------------------------------------------------------------
// ITE helpers
// ---------------------------------------------------------------------------

void EufSolver::initializeBoolConstants() {
    trueTerm_ = termManager_.internTrueConstant();
    falseTerm_ = termManager_.internFalseConstant();
    egraph_.setTrueTerm(trueTerm_);
    egraph_.setFalseTerm(falseTerm_);
    egraph_.ensureTerm(trueTerm_);
    egraph_.ensureTerm(falseTerm_);

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

void EufSolver::registerNewIteTerms() {
    size_t n = termManager_.termCount();
    for (; nextTermToScan_ < n; ++nextTermToScan_) {
        auto term = static_cast<EufTermId>(nextTermToScan_);
        const auto& node = termManager_.node(term);
        if (!termManager_.isIteSymbol(node.symbol) || node.args.size() != 3)
            continue;
        if (iteOfResult_.find(term) != iteOfResult_.end())
            continue;  // hash-cons duplicate

        EufTermId cond = node.args[0];
        EufTermId thenTerm = node.args[1];
        EufTermId elseTerm = node.args[2];
        registerIte(term, cond, thenTerm, elseTerm);
    }
}

void EufSolver::registerIte(EufTermId result, EufTermId cond,
                            EufTermId thenTerm, EufTermId elseTerm) {
    IteId id = static_cast<IteId>(iteRecords_.size());
    iteRecords_.push_back({result, cond, thenTerm, elseTerm});
    iteOfResult_[result] = id;

    classInfo(egraph_.rep(cond)).condUses.push_back(id);
    classInfo(egraph_.rep(thenTerm)).thenUses.push_back(id);
    classInfo(egraph_.rep(elseTerm)).elseUses.push_back(id);

    tryFireIte(id);
}

void EufSolver::tryFireIte(IteId id) {
    const auto& r = iteRecords_[id];
    EClassId c  = egraph_.rep(r.cond);
    EClassId th = egraph_.rep(r.thenTerm);
    EClassId el = egraph_.rep(r.elseTerm);
    EClassId res = egraph_.rep(r.result);

    auto cMark = classInfo(c).boolMark;

    if (cMark == BoolConstMark::True && !egraph_.same(res, th)) {
        mergeQueue_.push_back(PendingMerge{
            r.result, r.thenTerm,
            MergeReason{MergeReasonKind::IteTrue, SatLit{}, 0,
                        r.cond, trueTerm_}
        });
    }
    if (cMark == BoolConstMark::False && !egraph_.same(res, el)) {
        mergeQueue_.push_back(PendingMerge{
            r.result, r.elseTerm,
            MergeReason{MergeReasonKind::IteFalse, SatLit{}, 0,
                        r.cond, falseTerm_}
        });
    }
    if (th == el && !egraph_.same(res, th)) {
        mergeQueue_.push_back(PendingMerge{
            r.result, r.thenTerm,
            MergeReason{MergeReasonKind::IteBranchesEqual, SatLit{}, 0,
                        r.thenTerm, r.elseTerm}
        });
    }
}

void EufSolver::onEclassMerged(EClassId kept, EClassId killed) {
    auto& kInfo = classInfo(kept);
    auto& dInfo = classInfo(killed);

    // Trail
    IteOccMoveTrail trail;
    trail.kept = kept; trail.killed = killed;
    trail.keptCondOldSize  = kInfo.condUses.size();
    trail.keptThenOldSize  = kInfo.thenUses.size();
    trail.keptElseOldSize  = kInfo.elseUses.size();
    trail.killedCondOldSize = dInfo.condUses.size();
    trail.killedThenOldSize = dInfo.thenUses.size();
    trail.killedElseOldSize = dInfo.elseUses.size();

    // Append killed -> kept
    for (IteId iid : dInfo.condUses) kInfo.condUses.push_back(iid);
    for (IteId iid : dInfo.thenUses) kInfo.thenUses.push_back(iid);
    for (IteId iid : dInfo.elseUses) kInfo.elseUses.push_back(iid);

    trail.movedCondCount = dInfo.condUses.size();
    trail.movedThenCount = dInfo.thenUses.size();
    trail.movedElseCount = dInfo.elseUses.size();

    dInfo.condUses.clear();
    dInfo.thenUses.clear();
    dInfo.elseUses.clear();

    // boolMark
    trail.keptOldMark  = kInfo.boolMark;
    trail.killedOldMark = dInfo.boolMark;

    BoolConstMark merged = mergeBoolMark(kInfo.boolMark, dInfo.boolMark);
    kInfo.boolMark = merged;
    dInfo.boolMark = BoolConstMark::None;

    iteOccMoveTrail_.push_back(trail);

    // Both -> conflict
    if (merged == BoolConstMark::Both) {
        pendingConflict_ = TheoryConflict{
            egraph_.explainEquality(trueTerm_, falseTerm_).reasons
        };
        return;
    }

    // boolMark 新变成 const -> 扫描 condUses
    bool keptWasConst = (trail.keptOldMark == BoolConstMark::True ||
                         trail.keptOldMark == BoolConstMark::False);
    bool nowConst = (merged == BoolConstMark::True ||
                     merged == BoolConstMark::False);
    if (nowConst && !keptWasConst) {
        for (IteId iid : kInfo.condUses) tryFireIte(iid);
    }

    // then/else 可能相等 -> 扫描所有 thenUses/elseUses
    for (IteId iid : kInfo.thenUses) tryFireIte(iid);
    for (IteId iid : kInfo.elseUses) tryFireIte(iid);
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
    egraph_.ensureTerm(trueTerm);
    egraph_.ensureTerm(falseTerm);

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
        std::cerr << "[EUF] assertLit: intern failed lhs=" << payload.lhs
                  << " rhs=" << payload.rhs << "\n";
        return;
    }

    egraph_.ensureTerm(lhs);
    egraph_.ensureTerm(rhs);

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

TheoryCheckResult EufSolver::check(TheoryLemmaDatabase& /*lemmaDb*/) {
    NO_DBG << "[EUF] check begin\n";
    if (pendingUnknown_) {
        NO_DBG << "[EUF] pendingUnknown -> Unknown\n";
        return TheoryCheckResult::unknown();
    }
    if (pendingConflict_) {
        NO_DBG << "[EUF] pendingConflict -> Conflict\n";
        return TheoryCheckResult::mkConflict(*pendingConflict_);
    }

    registerNewIteTerms();

    // 唯一 saturation loop：drain SAT decisions + congruence + ITE
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

        auto mr = egraph_.merge(req.a, req.b, req.reason);
        if (!mr.merged) continue;

        // ITE metadata：只 enqueue，不递归 merge
        onEclassMerged(mr.kept, mr.killed);
        if (pendingConflict_) {
            return TheoryCheckResult::mkConflict(*pendingConflict_);
        }

        // congruence closure：把新 merges 推到同一 queue
        egraph_.refreshCongruence(mr.kept, mr.killed, mergeQueue_);
    }

    // true/false conflict
    if (trueTerm_ != NullEufTerm && falseTerm_ != NullEufTerm &&
        egraph_.same(trueTerm_, falseTerm_)) {
        auto er = egraph_.explainEquality(trueTerm_, falseTerm_);
        if (er.ok) {
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
        }
        NO_DBG << "[EUF] true=same but explain failed -> Unknown\n";
        return TheoryCheckResult::unknown();
    }

    // disequality conflicts
    for (const auto& d : disequalities_) {
        if (egraph_.same(d.lhs, d.rhs)) {
            auto er = egraph_.explainEquality(d.lhs, d.rhs);
            if (er.ok) {
                er.reasons.push_back(d.reason);
                NO_DBG << "[EUF] disequality conflict reasons: " << debug::fmtClause(er.reasons) << "\n";
                return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
            }
            NO_DBG << "[EUF] disequality same but explain failed -> Unknown\n";
            return TheoryCheckResult::unknown();
        }
    }

    // shared disequality conflicts
    for (const auto& d : sharedDisequalities_) {
        if (egraph_.same(d.lhs, d.rhs)) {
            auto er = egraph_.explainEquality(d.lhs, d.rhs);
            if (er.ok) {
                er.reasons.push_back(d.reason);
                NO_DBG << "[EUF] shared disequality conflict reasons: " << debug::fmtClause(er.reasons) << "\n";
                return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
            }
            NO_DBG << "[EUF] shared disequality same but explain failed -> Unknown\n";
            return TheoryCheckResult::unknown();
        }
    }

    std::cerr << "[EUF] Consistent disequalities=" << disequalities_.size()
              << " sharedDisequalities=" << sharedDisequalities_.size() << "\n";
    return TheoryCheckResult::consistent();
}

// ---------------------------------------------------------------------------
// Nelson-Oppen combination hooks
// ---------------------------------------------------------------------------

EufTermId EufSolver::internSharedConstant(SharedTermId s) {
    auto it = sharedTermToEufTerm_.find(s);
    if (it != sharedTermToEufTerm_.end()) return it->second;

    if (!sharedTermRegistry_ || !coreIr_) return NullEufTerm;
    const auto* st = sharedTermRegistry_->get(s);
    if (!st) return NullEufTerm;

    EufTermId t = termManager_.intern(st->coreExpr, const_cast<CoreIr&>(*coreIr_));
    if (t != NullEufTerm) {
        sharedTermToEufTerm_[s] = t;
        egraph_.ensureTerm(t);
    }
    return t;
}

EufTermId EufSolver::internEufExpr(ExprId eid) {
    if (!coreIr_) return NullEufTerm;
    EufTermId t = termManager_.intern(eid, const_cast<CoreIr&>(*coreIr_));
    if (t != NullEufTerm) {
        egraph_.ensureTerm(t);
    }
    return t;
}

TheoryCheckResult EufSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    ensureSnapshotForLevel(level);

    EufTermId ta = internSharedConstant(a);
    EufTermId tb = internSharedConstant(b);
    if (ta == NullEufTerm || tb == NullEufTerm) {
        return TheoryCheckResult::consistent();
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
        return TheoryCheckResult::consistent();
    }

    if (egraph_.same(ta, tb)) {
        auto er = egraph_.explainEquality(ta, tb);
        if (er.ok) {
            std::cerr << "[EUF-IDISEQ] same a=" << a << " b=" << b << " reason=" << (reason.sign?"+":"") << reason.var;
            std::cerr << " explain=";
            for (auto& lit : er.reasons) std::cerr << (lit.sign?"+":"") << lit.var << " ";
            std::cerr << "\n";
            er.reasons.push_back(reason);
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
        }
        return TheoryCheckResult::unknown();
    }

    const auto& na = termManager_.node(ta);
    const auto& nb = termManager_.node(tb);
    if (na.args.empty() && nb.args.empty() && na.symbol != nb.symbol) {
        return TheoryCheckResult::consistent();
    }

    sharedDisequalities_.push_back({ta, tb, reason, level, trail_.size()});
    return TheoryCheckResult::consistent();
}

std::vector<TheorySolver::SharedEqualityPropagation>
EufSolver::getDeducedSharedEqualities() {
    std::vector<SharedEqualityPropagation> result;
    if (!sharedTermRegistry_) return result;

    const auto& allShared = sharedTermRegistry_->allSharedTerms();
    std::cerr << "[EUF-DEDUCE] sharedTerms=" << allShared.size() << "\n";
    for (size_t i = 0; i < allShared.size(); ++i) {
        EufTermId ti = internSharedConstant(allShared[i]);
        if (ti == NullEufTerm) continue;
        for (size_t j = i + 1; j < allShared.size(); ++j) {
            EufTermId tj = internSharedConstant(allShared[j]);
            if (tj == NullEufTerm) continue;
            if (egraph_.same(ti, tj)) {
                auto er = egraph_.explainEquality(ti, tj);
                if (er.ok) {
                    std::cerr << "[EUF-DEDUCE] EQ st=" << allShared[i] << " st=" << allShared[j] << " reasons=" << er.reasons.size() << "\n";
                    result.push_back({allShared[i], allShared[j], std::move(er.reasons)});
                }
            }
        }
    }
    return result;
}

} // namespace nlcolver
