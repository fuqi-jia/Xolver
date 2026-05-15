#include "theory/euf/EufSolver.h"
#include "theory/DebugTrace.h"
#include <iostream>
#include "theory/TheoryLemmaDatabase.h"
#include <cassert>
#include <algorithm>
#include <iostream>

namespace nlcolver {

EufSolver::EufSolver() : egraph_(termManager_) {}

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
}

void EufSolver::ensureSnapshotForLevel(int level) {
    // CDCL decision levels are monotonically entered.
    // backtrackToLevel() pops higher-level snapshots before re-entering.
    assert(levelSnapshots_.empty() || levelSnapshots_.back().level <= level);

    if (levelSnapshots_.empty() || levelSnapshots_.back().level < level) {
        levelSnapshots_.push_back({
            level,
            trail_.size(),
            egraph_.snapshot()
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

void EufSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) {
    if (!std::holds_alternative<EufAtomPayload>(atom.payload)) return;
    const auto& payload = std::get<EufAtomPayload>(atom.payload);

    // Ensure decision-level snapshot exists
    ensureSnapshotForLevel(level);

    // Lazily intern true/false constants
    EufTermId trueTerm = termManager_.internTrueConstant();
    EufTermId falseTerm = termManager_.internFalseConstant();
    egraph_.setTrueTerm(trueTerm);
    egraph_.setFalseTerm(falseTerm);
    egraph_.ensureTerm(trueTerm);
    egraph_.ensureTerm(falseTerm);

    // Intern lhs/rhs (monotonic)
    EufTermId lhs = termManager_.intern(payload.lhs, *coreIr_);
    EufTermId rhs = termManager_.intern(payload.rhs, *coreIr_);
    if (lhs == NullEufTerm || rhs == NullEufTerm) return;

    egraph_.ensureTerm(lhs);
    egraph_.ensureTerm(rhs);

    // Bool formula-position semantics:
    // Atomizer encodes Bool terms as (= term true)
    // If (= b true) assigned true  -> merge(b, true)
    // If (= b true) assigned false -> merge(b, false)
    if (payload.kind == EufAtomKind::BoolTermAsFormula) {
        EufTermId target = value ? trueTerm : falseTerm;
        trail_.push_back({level, reason, atom, value});
        MergeReason mr;
        mr.kind = MergeReasonKind::AssertedEquality;
        mr.assertedLit = reason;
        auto status = egraph_.merge(lhs, target, mr);
        if (status == MergeStatus::SortMismatch) {
            pendingUnknown_ = true;
        }
        return;
    }

    // Normal EUF equality/disequality
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
        mr.assertedLit = reason;
        auto status = egraph_.merge(lhs, rhs, mr);
        if (status == MergeStatus::SortMismatch) {
            pendingUnknown_ = true;
        }
    } else {
        disequalities_.push_back({lhs, rhs, reason, level, trailIdx});
    }
}

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

    // Process any pending congruence merges (e.g. from newly-interned app terms)
    egraph_.processMergeQueue();

    // true/false invariant
    EufTermId tTrue = termManager_.trueConstant();
    EufTermId tFalse = termManager_.falseConstant();
    if (tTrue != NullEufTerm && tFalse != NullEufTerm && egraph_.same(tTrue, tFalse)) {
        auto er = egraph_.explainEquality(tTrue, tFalse);
        if (er.ok) {
            for (auto& lit : er.reasons) lit = lit.negated();
            NO_DBG << "[EUF] true=false conflict: " << debug::fmtClause(er.reasons) << "\n";
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
                for (auto& lit : er.reasons) lit = lit.negated();
                er.reasons.push_back(d.reason.negated());
                NO_DBG << "[EUF] disequality conflict: " << debug::fmtClause(er.reasons) << "\n";
                return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
            }
            NO_DBG << "[EUF] disequality same but explain failed -> Unknown\n";
            return TheoryCheckResult::unknown();
        }
    }

    NO_DBG << "[EUF] Consistent\n";
    return TheoryCheckResult::consistent();
}

// ---------------------------------------------------------------------------
// Nelson-Oppen combination hooks
// ---------------------------------------------------------------------------

EufTermId EufSolver::internSharedTerm(SharedTermId s) {
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

TheoryCheckResult EufSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    ensureSnapshotForLevel(level);

    EufTermId ta = internSharedTerm(a);
    EufTermId tb = internSharedTerm(b);
    if (ta == NullEufTerm || tb == NullEufTerm) {
        return TheoryCheckResult::consistent();
    }

    MergeReason mr;
    mr.kind = MergeReasonKind::AssertedEquality;
    mr.assertedLit = reason;
    auto status = egraph_.merge(ta, tb, mr);
    if (status == MergeStatus::SortMismatch) {
        return TheoryCheckResult::unknown();
    }
    return TheoryCheckResult::consistent();
}

TheoryCheckResult EufSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {

    ensureSnapshotForLevel(level);

    EufTermId ta = internSharedTerm(a);
    EufTermId tb = internSharedTerm(b);
    if (ta == NullEufTerm || tb == NullEufTerm) {
        return TheoryCheckResult::consistent();
    }

    if (egraph_.same(ta, tb)) {
        auto er = egraph_.explainEquality(ta, tb);
        if (er.ok) {
            for (auto& lit : er.reasons) lit = lit.negated();
            er.reasons.push_back(reason.negated());
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(er.reasons)});
        }
        return TheoryCheckResult::unknown();
    }

    sharedDisequalities_.push_back({ta, tb, reason, level, trail_.size()});
    return TheoryCheckResult::consistent();
}

std::vector<TheorySolver::SharedEqualityPropagation>
EufSolver::getDeducedSharedEqualities() {
    std::vector<SharedEqualityPropagation> result;
    if (!sharedTermRegistry_) return result;

    const auto& allShared = sharedTermRegistry_->allSharedTerms();
    for (size_t i = 0; i < allShared.size(); ++i) {
        EufTermId ti = internSharedTerm(allShared[i]);
        if (ti == NullEufTerm) continue;
        for (size_t j = i + 1; j < allShared.size(); ++j) {
            EufTermId tj = internSharedTerm(allShared[j]);
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

} // namespace nlcolver
