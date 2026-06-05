#include "theory/arith/nra/core/CdcacSolver.h"
#include "theory/arith/nra/core/CdcacCore.h"
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/nra/core/CdcacCache.h"
#include "theory/arith/nra/simplex/VarOrderSelector.h"
#include "theory/arith/linear/LinearExpr.h"
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <cstdlib>
#include <iostream>

namespace xolver {

CdcacSolver::CdcacSolver(PolynomialKernel* kernel)
    : kernel_(kernel) {
    if (const char* e = std::getenv("XOLVER_NRA_VARORDER_SIMPLEX"))
        simplexVarOrder_ = (e[0]=='1'||e[0]=='t'||e[0]=='T'||e[0]=='y'||e[0]=='Y');
#ifdef XOLVER_HAS_LIBPOLY
    std::cerr << "[CDCAC-SOLVER] constructing with libpoly" << std::endl;
    algebra_ = std::make_unique<LibpolyBackend>(kernel_);
    core_ = std::make_unique<CdcacCore>(kernel_, algebra_.get());
    std::cerr << "[CDCAC-SOLVER] core_=" << (core_ ? "yes" : "no")
              << " algebra_=" << (algebra_ ? "yes" : "no") << std::endl;
#else
    std::cerr << "[CDCAC-SOLVER] constructing WITHOUT libpoly" << std::endl;
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

    // Sort variables lexicographically for a deterministic base / tie-break.
    std::sort(varOrderNames.begin(), varOrderNames.end());
    if (simplexVarOrder_ && varOrderNames.size() > 1) {
        // XOLVER_NRA_VARORDER_SIMPLEX: degree-stratified order + frontScore
        // tie-break (opt-in override).
        varOrderNames = computeCdcacVarOrder(*kernel_, input.constraints, varOrderNames);
    } else if (varOrderNames.size() > 1) {
        // DEFAULT: Brown's CAD heuristic — eliminate (PROJECT) the lowest total
        // degree variable FIRST, i.e. ASSIGN it LAST. CDCAC is highly
        // order-sensitive and the previous alphabetical default produced WRONG
        // UNSAT (gdb+delta-debug confirmed: Geogebra IsoRightTriangle-Bottema1.4b,
        // minimised to {m>0, v10^2=1/4, v11^2=1/2, m-constraint}): when a variable
        // m that is DETERMINED by later variables (linear, in a single trilinear
        // constraint) is assigned FIRST, its axis is delineated only by its own
        // bound; the covering samples one sector rep (m=1), which conflicts, and
        // the whole feasible sector (m>~4.12) is wrongly excluded because the
        // feasibility boundary (the eliminated-variable discriminant) is never a
        // delineation root -> false UNSAT. Sorting highest-degree FIRST keeps such
        // determined variables at the deepest lift level where an exact root pins
        // them. The lazy CacEngine already uses this heuristic and is sound here;
        // this brings the Collins/Lazard CdcacCore into line. Stable over the
        // lexicographic base for determinism. (XOLVER_NRA_VARORDER_ASC opts back
        // into the old ascending order for differential.)
        static const bool ascending = std::getenv("XOLVER_NRA_VARORDER_ASC") != nullptr;
        std::unordered_map<std::string, int> degSum;
        for (const auto& name : varOrderNames) degSum[name] = 0;
        for (const auto& c : active_) {
            for (const auto& name : varOrderNames) {
                if (auto d = kernel_->degree(c.poly, name)) degSum[name] += *d;
            }
        }
        std::stable_sort(varOrderNames.begin(), varOrderNames.end(),
            [&degSum, ascending](const std::string& a, const std::string& b) {
                return ascending ? (degSum[a] < degSum[b]) : (degSum[a] > degSum[b]);
            });
    }
    for (const auto& name : varOrderNames) {
        input.varOrder.push_back(kernel_->getOrCreateVar(name));
    }

#ifndef NDEBUG
    std::cerr << "[CDCAC-SOLVER] solving with " << input.constraints.size()
              << " constraints, " << input.varOrder.size() << " vars" << std::endl;
#endif
    CdcacResult result = core_->solve(input);
#ifndef NDEBUG
    std::cerr << "[CDCAC-SOLVER] result status=" << (int)result.status << std::endl;
#endif

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

RealValue CdcacSolver::sampleValueToRealValue(const RealAlg& v) const {
    if (v.kind == RealAlg::Kind::Rational) {
        return RealValue::fromMpq(v.rational);
    }
    const AlgebraicRoot& root = v.root;
    if (!algebra_ || root.definingPoly == NullUniPolyId) {
        // Degenerate (no defining polynomial): fall back to a rational
        // midpoint approximation of the isolation interval.
        mpq_class mid = (root.lower + root.upper) / 2;
        return RealValue::fromMpq(mid);
    }
    // The backend stores coefficients high-to-low; AlgebraicNumber wants
    // low-to-high (coefficients[i] = coeff of x^i).
    const auto& hiToLo = algebra_->getUni(root.definingPoly);
    AlgebraicNumber an;
    an.coefficients.assign(hiToLo.rbegin(), hiToLo.rend());
    an.lower = root.lower;
    an.upper = root.upper;
    an.lowerOpen = true;
    an.upperOpen = true;
    return RealValue::fromAlgebraic(std::move(an));
}

} // namespace xolver
