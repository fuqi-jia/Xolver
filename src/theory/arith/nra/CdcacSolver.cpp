#include "theory/arith/nra/CdcacSolver.h"
#include "theory/arith/nra/CdcacCore.h"
#include "theory/arith/nra/LibpolyBackend.h"
#include "theory/arith/nra/CdcacCache.h"
#include "theory/arith/linear/LinearExpr.h"
#include <unordered_set>
#include <algorithm>

namespace nlcolver {

CdcacSolver::CdcacSolver(PolynomialKernel* kernel)
    : kernel_(kernel) {
#ifdef NLCOLVER_HAS_LIBPOLY
    algebra_ = std::make_unique<LibpolyBackend>(kernel_);
    core_ = std::make_unique<CdcacCore>(kernel_, algebra_.get());
#endif
}

CdcacSolver::~CdcacSolver() = default;

void CdcacSolver::reset() {
    active_.clear();
    trail_.clear();
    scopeStack_.clear();
    pendingConflict_.reset();
    pendingUnknown_.reset();
    if (cache_) cache_->clear();
}

void CdcacSolver::push() {
    scopeStack_.push_back({active_.size(), trail_.size()});
    if (cache_) cache_->push();
}

void CdcacSolver::pop(uint32_t n) {
    for (uint32_t i = 0; i < n && !scopeStack_.empty(); ++i) {
        const auto& snap = scopeStack_.back();
        active_.resize(snap.activeSize);
        trail_.resize(snap.trailSize);
        scopeStack_.pop_back();
    }
    if (cache_) cache_->pop(n);
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
            conflictLits.push_back(c.reason);
        }
    }

    if (!conflictLits.empty()) {
        return TheoryCheckResult::mkConflict(TheoryConflict{conflictLits});
    }

    if (!hasNonConstant) {
        return TheoryCheckResult::consistent();
    }

    // P2a: delegate non-constant constraints to CDCAC core
    if (!core_ || !algebra_) {
        return TheoryCheckResult::unknown();
    }

    // Build CdcacInput from active constraints
    CdcacInput input;
    std::unordered_set<std::string> varNames;
    std::vector<std::string> varOrderNames;

    for (const auto& c : active_) {
        CdcacConstraint cc;
        cc.poly = c.poly;
        cc.rel = c.rel;
        cc.reason = c.reason;
        input.constraints.push_back(std::move(cc));

        for (const auto& v : kernel_->variables(c.poly)) {
            if (varNames.insert(v).second) {
                varOrderNames.push_back(v);
            }
        }
    }

    // Sort variables lexicographically for deterministic order
    std::sort(varOrderNames.begin(), varOrderNames.end());
    for (const auto& name : varOrderNames) {
        input.varOrder.push_back(kernel_->getOrCreateVar(name));
    }

    CdcacResult result = core_->solve(input);

    switch (result.status) {
        case CdcacStatus::Sat:
            lastModel_ = std::move(result.model);
            return TheoryCheckResult::consistent();
        case CdcacStatus::Unsat: {
            std::vector<SatLit> reasons;
            if (result.unsat) {
                reasons = ReasonManager::minimize(result.unsat->covering);
            }
            return TheoryCheckResult::mkConflict(ReasonManager::toConflict(reasons));
        }
        case CdcacStatus::Unknown:
            return TheoryCheckResult::unknown();
    }

    return TheoryCheckResult::unknown();
}

TheoryCheckResult CdcacSolver::check(CdcacEffort /*effort*/, void* /*trail*/) {
    return check();
}

std::optional<SamplePoint> CdcacSolver::getModel() const {
    return lastModel_;
}

std::string CdcacSolver::formatAlgebraicRoot(const AlgebraicRoot& root) const {
    if (!algebra_ || root.definingPoly == NullUniPolyId) {
        // Fallback: use midpoint of isolating interval
        mpq_class mid = (root.lower + root.upper);
        mid /= 2;
        return mid.get_str();
    }

    const auto& coeffs = algebra_->getUni(root.definingPoly);
    std::string result = "(AlgebraicNumber (poly";
    for (const auto& c : coeffs) {
        result += " " + c.get_str();
    }
    result += ") (lower " + root.lower.get_str() + ")";
    result += " (upper " + root.upper.get_str() + "))";
    return result;
}

} // namespace nlcolver
