#include "theory/arith/nra/CdcacSolver.h"
#include "theory/arith/linear/LinearExpr.h"

namespace nlcolver {

CdcacSolver::CdcacSolver(PolynomialKernel* kernel)
    : kernel_(kernel) {}

void CdcacSolver::reset() {
    active_.clear();
    trail_.clear();
    pendingConflict_.reset();
    pendingUnknown_.reset();
}

void CdcacSolver::assertConstraint(PolyId poly, Relation rel, SatLit reason, int level) {
    size_t oldSize = active_.size();
    active_.push_back({poly, rel, reason});
    trail_.push_back({level, oldSize});
}

void CdcacSolver::backtrack(int level) {
    while (!trail_.empty() && trail_.back().level > level) {
        active_.resize(trail_.back().activeSizeBefore);
        trail_.pop_back();
    }
    if (pendingConflict_ && pendingConflict_->level > level) {
        pendingConflict_.reset();
    }
    if (pendingUnknown_ && pendingUnknown_->level > level) {
        pendingUnknown_.reset();
    }
}

TheoryCheckResult CdcacSolver::check() {
    if (pendingConflict_) {
        return TheoryCheckResult::mkConflict(pendingConflict_->conflict);
    }

    if (pendingUnknown_) {
        return TheoryCheckResult::unknown();
    }

    if (active_.empty()) {
        return TheoryCheckResult::consistent();
    }

    std::vector<SatLit> conflictLits;
    bool hasNonConstant = false;

    for (const auto& c : active_) {
        if (!kernel_->isConstant(c.poly)) {
            hasNonConstant = true;
            continue;
        }
        mpq_class val = kernel_->toConstant(c.poly);
        bool ok = false;
        int s = (val > mpq_class(0)) ? 1 : (val < mpq_class(0)) ? -1 : 0;
        switch (c.rel) {
            case Relation::Eq:  ok = (s == 0); break;
            case Relation::Neq: ok = (s != 0); break;
            case Relation::Lt:  ok = (s <  0); break;
            case Relation::Leq: ok = (s <= 0); break;
            case Relation::Gt:  ok = (s >  0); break;
            case Relation::Geq: ok = (s >= 0); break;
        }
        if (!ok) {
            conflictLits.push_back(c.reason.negated());
        }
    }

    if (!conflictLits.empty()) {
        return TheoryCheckResult::mkConflict(TheoryConflict{conflictLits});
    }

    if (!hasNonConstant) {
        return TheoryCheckResult::consistent();
    }

    return TheoryCheckResult::unknown();
}

TheoryCheckResult CdcacSolver::check(TheoryEffort /*effort*/, void* /*trail*/) {
    return check();
}

} // namespace nlcolver
