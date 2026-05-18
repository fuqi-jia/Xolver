#include "theory/euf/EufSolver.h"
#include "theory/DebugTrace.h"
#include <iostream>
#include "theory/TheoryLemmaDatabase.h"
#include <cassert>
#include <algorithm>
#include <functional>
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

    classInfo_.clear();
    mergeQueue_.clear();
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
            mergeQueue_.size()
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

        mergeQueue_.resize(snap.mergeQueueSize);

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

void EufSolver::onEclassMerged(EClassId kept, EClassId killed) {
    auto& kInfo = classInfo(kept);
    auto& dInfo = classInfo(killed);

    BoolConstMark merged = mergeBoolMark(kInfo.boolMark, dInfo.boolMark);
    kInfo.boolMark = merged;
    dInfo.boolMark = BoolConstMark::None;

    // Both -> conflict
    if (merged == BoolConstMark::Both) {
        pendingConflict_ = TheoryConflict{
            egraph_.explainEquality(trueTerm_, falseTerm_).reasons
        };
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
                  << " rhs=" << payload.rhs << " -> pendingUnknown\n";
        pendingUnknown_ = true;
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

TheoryCheckResult EufSolver::check(TheoryLemmaDatabase& /*lemmaDb*/, TheoryEffort) {
    NO_DBG << "[EUF] check begin\n";
    if (pendingUnknown_) {
        NO_DBG << "[EUF] pendingUnknown -> Unknown\n";
        return TheoryCheckResult::unknown();
    }
    if (pendingConflict_) {
        NO_DBG << "[EUF] pendingConflict -> Conflict\n";
        return TheoryCheckResult::mkConflict(*pendingConflict_);
    }

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
