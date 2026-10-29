#include "base/RuntimeConfig.h"
#include "applications/satisfiability/smt/qfnia/NiaSolver.h"
#include "applications/satisfiability/smt/qfnia/NiaSolverDetail.h"
#include <algorithm>
#include "search/dl/DifferenceGraph.h"
#include "search/dl/BellmanFord.h"
#include "search/arith/Reasoner.h"
#include <random>
#include "search/nia/search/NiaLinearizationAdapter.h"
#include "search/nia/search/NiaIcpAdapter.h"
#include "search/icp/IcpTypes.h"
#include "search/nra/core/CdcacCore.h"
#include "search/nra/core/CdcacConstraint.h"
#include "search/nra/engine/ReasonManager.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "search/nra/backend/LibpolyBackend.h"
#include "search/nia/farkas/LeafFarkasLia.h"
#include "search/nra/reasoners/NlaCutsRunner.h"           // Stage 3 Phase C-3
#include "algebra/poly/RationalPolynomial.h"          // Stage 3 Phase C-3
#endif
#include "algebra/linear/LinearExpr.h"
#include "applications/satisfiability/smt/qfnia/NiaLinearDecider.h"  // embedded bounded LIA search (nia.linear-decide)
#include "search/linearizer/NonlinearTermAbstraction.h"
#include "algebra/linear/LinearConstraintNormalizer.h"
#include "contracts/LogicFeatureDetector.h"
#include "search/presolve/Presolve.h"
#include "search/candidate/CompleteFiniteDomainEnumerator.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "evidence/ArithModelValidator.h"
#include "base/EnvParam.h"
#include <functional>
#include <set>
#include "search/nia/farkas/FarkasOrDetector.h"
#include "search/nia/farkas/FarkasOrSolver.h"
#include "search/nia/farkas/FarkasOrModelAssembler.h"
#include "base/MpqUtils.h"
#include <chrono>
#include <iostream>

#include <unordered_set>
#include <cstdlib>
namespace xolver {

// NOTE: This translation unit was split out of NiaSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

std::optional<TheoryCheckResult> NiaSolver::stageBranch(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    if (auto lemma = buildBranchLemma(normalized_, domains_, lemmaDb)) {
        return TheoryCheckResult::mkLemma(*lemma);
    }
    return TheoryCheckResult::unknown("NIA: no progress (finite domain not closed, branch lemma failed, local search failed)");
}

std::optional<TheoryCheckResult> NiaSolver::stagePendingLemma(TheoryLemmaStorage&, TheoryEffort) {
    if (!pendingLinLemmas_.empty()) {
        auto lemma = std::move(pendingLinLemmas_.front());
        pendingLinLemmas_.pop_front();
        return TheoryCheckResult::mkLemma(lemma);
    }
    return std::nullopt;
}

bool NiaSolver::relationSatisfied(const mpq_class& val, Relation rel) const {
    switch (rel) {
        case Relation::Eq:  return val == 0;
        case Relation::Neq: return val != 0;
        case Relation::Lt:  return val <  0;
        case Relation::Leq: return val <= 0;
        case Relation::Gt:  return val >  0;
        case Relation::Geq: return val >= 0;
    }
    return false;
}

std::optional<TheoryLemma> NiaSolver::buildBranchLemma(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const DomainStore& domains,
    TheoryLemmaStorage& lemmaDb) {

    if (!registry_) return std::nullopt;

    auto allVars = collectVars(constraints, *kernel_);
    if (allVars.empty()) return std::nullopt;

    // Collect candidate variables with their domain info
    struct Candidate {
        std::string var;
        bool hasLower;
        bool hasUpper;
        mpz_class lower;
        mpz_class upper;
        mpz_class rangeSize; // upper - lower, or 0 if unbounded
        int priority; // 0 = both bounds, 1 = one bound, 2 = no bounds
    };
    std::vector<Candidate> candidates;

    for (const auto& var : allVars) {
        const IntDomain* d = domains.getDomain(var);
        Candidate c{var, false, false, 0, 0, 0, 2};
        if (d) {
            c.hasLower = d->hasLower;
            c.hasUpper = d->hasUpper;
            if (c.hasLower) c.lower = d->lower.value;
            if (c.hasUpper) c.upper = d->upper.value;
            if (c.hasLower && c.hasUpper) {
                c.rangeSize = c.upper - c.lower;
                c.priority = 0;
                // Skip singleton domains (already fixed)
                if (c.rangeSize <= 0) continue;
            } else if (c.hasLower || c.hasUpper) {
                c.priority = 1;
            }
        }
        candidates.push_back(c);
    }

    if (candidates.empty()) return std::nullopt;

    // Sort by bound priority, then by descending domain width.
    std::sort(candidates.begin(), candidates.end(),
        [&](const Candidate& a, const Candidate& b) {
            if (a.priority != b.priority) return a.priority < b.priority;
            return a.rangeSize > b.rangeSize;
        });

    for (const auto& cand : candidates) {
        mpz_class k;
        if (cand.hasLower && cand.hasUpper) {
            k = (cand.lower + cand.upper) / 2;
        } else if (cand.hasLower) {
            k = cand.lower;
        } else if (cand.hasUpper) {
            k = cand.upper - 1;
        } else {
            // Unbounded: only center split at k=0
            k = 0;
        }

        const IntDomain* d = domains.getDomain(cand.var);
        bool hasBothBounds = d && d->hasLower && d->hasUpper;
        bool isUnbounded = !cand.hasLower && !cand.hasUpper;
        int& count = branchCountPerVar_[cand.var];
        if (isUnbounded && count >= MAX_UNBOUNDED_SPLITS) continue;
        if (!hasBothBounds && !isUnbounded && count >= MAX_SINGLE_BOUND_SPLITS) continue;

        // Duplicate suppression: skip if already emitted
        BranchSplitKey key{cand.var, k};
        if (emittedSplits_.count(key)) continue;

        PolyId xPoly = kernel_->mkVar(kernel_->getOrCreateVar(cand.var));

        // x <= k
        SatLit litLeq = registry_->getOrCreatePolynomialAtom(
            xPoly, Relation::Leq, mpq_class(k), TheoryId::NIA);

        // x >= k+1
        SatLit litGeq = registry_->getOrCreatePolynomialAtom(
            xPoly, Relation::Geq, mpq_class(k + 1), TheoryId::NIA);

        TheoryLemma lemma{{litLeq, litGeq}};

        if (lemmaDb.contains(lemma)) continue;
        lemmaDb.insertIfNew(lemma);
        emittedSplits_.insert(key);
        ++count;

        return lemma;
    }

    return std::nullopt;
}

} // namespace xolver
