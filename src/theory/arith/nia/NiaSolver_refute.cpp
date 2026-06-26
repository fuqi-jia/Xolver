#include "theory/arith/nia/NiaSolver.h"
#include "theory/arith/nia/NiaSolverDetail.h"  // collectVars / dispatch-signature helpers (shared across split TUs)
#include <algorithm>
#include "theory/arith/dl/DifferenceGraph.h"
#include "theory/arith/dl/BellmanFord.h"
#include "theory/arith/nia/preprocess/VariablePartition.h"
#include "theory/arith/Reasoner.h"
#include <random>
#include "theory/arith/nia/search/NiaLinearizationAdapter.h"
#include "theory/arith/nia/search/NiaIcpAdapter.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/arith/nra/core/CdcacCore.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/arith/nra/engine/ReasonManager.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/nia/farkas/LeafFarkasLia.h"
#include "theory/arith/nra/nla/NlaCutsRunner.h"           // Stage 3 Phase C-3
#include "theory/arith/poly/RationalPolynomial.h"          // Stage 3 Phase C-3
#endif
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/nia/search/NiaLinearDecider.h"  // embedded complete-LIA (nia.linear-decide)
#include "theory/arith/nia/reasoners/OmegaTest.h"        // nia.omega: sound linear-integer UNSAT
#include "theory/arith/nia/reasoners/SmallPrimeModular.h" // nia.small-prime-modular: GF(p) schedule
#include "theory/arith/nia/reasoners/IntBoundProp.h"      // nia.int-bound-prop: integer interval refutation
#include "theory/arith/linearizer/NonlinearTermAbstraction.h"
#include "theory/arith/linear/LinearConstraintNormalizer.h"
#include "theory/core/LogicFeatureDetector.h"
#include "theory/arith/presolve/Presolve.h"
#include "theory/arith/search/CompleteFiniteDomainEnumerator.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "proof/ArithModelValidator.h"
#include "util/EnvParam.h"
#include <functional>
#include <set>
#include "theory/arith/nia/farkas/FarkasOrDetector.h"
#include "theory/arith/nia/farkas/FarkasOrSolver.h"
#include "theory/arith/nia/farkas/FarkasOrModelAssembler.h"
#include "util/MpqUtils.h"
#include <chrono>
#include <iostream>

#include <unordered_set>
#include <cstdlib>
namespace xolver {

// NOTE: This translation unit was split out of NiaSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

std::optional<TheoryCheckResult> NiaSolver::stagePolyConflict(TheoryLemmaStorage&, TheoryEffort) {
    // Group active constraints by polynomial. Each is `P rel 0`, i.e. a sign
    // constraint on the value of P. Within one poly the constraints define an
    // interval-around-0 for P's value; if 0 is excluded AND P is pinned to 0 the
    // group is infeasible — a sound conflict (a single-poly Farkas certificate)
    // that needs no domain bounds. This is exactly the QF_UFNIA comparison
    // tautology: `-a+b` asserted both `<0` (a>b) and `>0` (a<b).
    struct Acc {
        bool hasUpper = false, upperStrict = false; SatLit upperReason{};
        bool hasLower = false, lowerStrict = false; SatLit lowerReason{};
        bool hasNeq = false; SatLit neqReason{};
    };
    // `P rel 0` ⟺ `-P flip(rel) 0`, so canonicalize each poly's sign (a form and
    // its negation share one group) — needed because `(= a b)` yields `a-b` while
    // `(>= a b)` yields `-a+b`. Sign-flip of the relation: Lt↔Gt, Leq↔Geq, Eq, Neq.
    auto flipRel = [](Relation r) -> Relation {
        switch (r) {
            case Relation::Lt:  return Relation::Gt;
            case Relation::Gt:  return Relation::Lt;
            case Relation::Leq: return Relation::Geq;
            case Relation::Geq: return Relation::Leq;
            default:            return r;  // Eq, Neq unchanged
        }
    };
    std::unordered_map<std::string, Acc> groups;
    for (const auto& c : active_) {
        auto it = polyCanonCache_.find(c.poly);
        if (it == polyCanonCache_.end()) {
            std::string sP = kernel_->toString(c.poly);
            std::string sN = kernel_->toString(kernel_->neg(c.poly));
            bool flip = sN < sP;
            it = polyCanonCache_.emplace(c.poly,
                     std::make_pair(flip ? sN : sP, flip)).first;
        }
        const std::string& key = it->second.first;
        Relation rel = it->second.second ? flipRel(c.rel) : c.rel;
        Acc& g = groups[key];
        switch (rel) {
            case Relation::Lt:  g.hasUpper = true; g.upperStrict = true; g.upperReason = c.reason; break;
            case Relation::Leq: if (!g.hasUpper) { g.hasUpper = true; g.upperReason = c.reason; } break;
            case Relation::Gt:  g.hasLower = true; g.lowerStrict = true; g.lowerReason = c.reason; break;
            case Relation::Geq: if (!g.hasLower) { g.hasLower = true; g.lowerReason = c.reason; } break;
            case Relation::Eq:
                if (!g.hasUpper) { g.hasUpper = true; g.upperReason = c.reason; }
                if (!g.hasLower) { g.hasLower = true; g.lowerReason = c.reason; }
                break;
            case Relation::Neq: g.hasNeq = true; g.neqReason = c.reason; break;
        }
    }
    // Fold in Nelson-Oppen interface disequalities (a != b shared by EUF). Their
    // diff poly a-b, canonicalized, joins the same group: if the comparison
    // bounds pin a-b to 0 (a=b) while EUF asserts a!=b, that is a sound conflict
    // the NIA-only sign reasoning would otherwise miss (the equality lives in
    // EUF, not NIA). Empty unless XOLVER_NIA_IFACE_LIFECYCLE populates them.
    for (const auto& ie : interfaceDisequalities_) {
        if (ie.diff == NullPoly) continue;
        auto it = polyCanonCache_.find(ie.diff);
        if (it == polyCanonCache_.end()) {
            std::string sP = kernel_->toString(ie.diff);
            std::string sN = kernel_->toString(kernel_->neg(ie.diff));
            bool flip = sN < sP;
            it = polyCanonCache_.emplace(ie.diff,
                     std::make_pair(flip ? sN : sP, flip)).first;
        }
        Acc& g = groups[it->second.first];
        g.hasNeq = true; g.neqReason = ie.reason;  // Neq is sign-invariant
    }
    for (auto& [poly, g] : groups) {
        // P bounded at 0 from both sides; a strict bound on either side makes the
        // only candidate (P=0) infeasible. Reasons: the two crossing constraints.
        if (g.hasUpper && g.hasLower && (g.upperStrict || g.lowerStrict)) {
            return TheoryCheckResult::mkConflict(
                TheoryConflict{{g.upperReason, g.lowerReason}});
        }
        // P pinned to 0 (P<=0 and P>=0) but asserted P!=0.
        if (g.hasUpper && g.hasLower && !g.upperStrict && !g.lowerStrict && g.hasNeq) {
            return TheoryCheckResult::mkConflict(
                TheoryConflict{{g.upperReason, g.lowerReason, g.neqReason}});
        }
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageDifferenceConflict(TheoryLemmaStorage&, TheoryEffort) {
    // Extract difference bounds `i - j <= c` from active `P rel 0` where
    // P == 1*i - 1*j + k, build a DifferenceGraph, and reuse the project's
    // BellmanFord engine to detect a negative cycle (a sound Farkas conflict).
    auto extractDiff = [&](PolyId P, std::string& vi, std::string& vj, mpz_class& k) -> bool {
        auto t = kernel_->terms(P);
        if (!t) return false;
        int nplus = 0, nminus = 0; k = 0;
        for (const auto& m : *t) {
            if (m.powers.empty()) { k += m.coefficient; continue; }
            if (m.powers.size() != 1 || m.powers[0].second != 1) return false;
            std::string v(kernel_->varName(m.powers[0].first));
            if (m.coefficient == 1)       { if (nplus++)  return false; vi = v; }
            else if (m.coefficient == -1) { if (nminus++) return false; vj = v; }
            else return false;
        }
        return nplus == 1 && nminus == 1;
    };
    DifferenceGraph<mpz_class> graph;
    // edge for `x - y <= c`: BellmanFord relaxes dist[to] <= dist[from] + w,
    // i.e. to - from <= w, so from=y, to=x, w=c.
    auto addBound = [&](const std::string& x, const std::string& y,
                        const mpz_class& c, SatLit r) {
        graph.addEdge(graph.getOrCreateNode(y), graph.getOrCreateNode(x), c, r);
    };
    bool any = false;
    for (const auto& con : active_) {
        std::string vi, vj; mpz_class k;
        if (!extractDiff(con.poly, vi, vj, k) || vi == vj) continue;
        // poly = vi - vj + k ; `poly rel 0`  ==>  vi - vj rel -k
        switch (con.rel) {
            case Relation::Leq: addBound(vi, vj, -k, con.reason); any = true; break;
            case Relation::Lt:  addBound(vi, vj, -k - 1, con.reason); any = true; break;
            case Relation::Geq: addBound(vj, vi, k, con.reason); any = true; break;
            case Relation::Gt:  addBound(vj, vi, k - 1, con.reason); any = true; break;
            case Relation::Eq:
                addBound(vi, vj, -k, con.reason);
                addBound(vj, vi, k, con.reason);
                any = true; break;
            case Relation::Neq: break;
        }
        if (graph.numNodes() > 96) return std::nullopt;  // keep BF cheap on big problems
    }
    // Fold Nelson-Oppen interface equalities (a == b, shared by EUF — e.g. the
    // intmodtotal ite's `itevar = r`) as bidirectional difference edges so the
    // difference chain can cross the theory boundary. (Interface diseqs are not
    // difference BOUNDS; stagePolyConflict already handles them.)
    for (const auto& ie : interfaceEqualities_) {
        if (ie.diff == NullPoly) continue;
        std::string vi, vj; mpz_class k;
        if (!extractDiff(ie.diff, vi, vj, k) || vi == vj) continue;
        addBound(vi, vj, -k, ie.reason);   // vi - vj <= -k
        addBound(vj, vi, k, ie.reason);     // vi - vj >= -k
        any = true;
        if (graph.numNodes() > 96) return std::nullopt;
    }
    if (!any) return std::nullopt;
    BellmanFord<mpz_class> bf;
    auto res = bf.runFull(graph);
    if (!res.negativeCycle) return std::nullopt;
    std::vector<SatLit> reasons;
    for (EdgeId eid : res.cycle) {
        SatLit r = graph.edge(eid).reason;
        if (std::none_of(reasons.begin(), reasons.end(),
                         [&](SatLit x){ return x.var == r.var && x.sign == r.sign; }))
            reasons.push_back(r);
    }
    if (reasons.empty()) return std::nullopt;
    return TheoryCheckResult::mkConflict(TheoryConflict{reasons});
}

std::optional<TheoryCheckResult> NiaSolver::stageDomainInference(TheoryLemmaStorage&, TheoryEffort) {
    // 3. Reset domains
    domains_.reset();

    static const bool domDiag = xolver::env::diag("NIA_DOM_DIAG");
    if (domDiag) {
        std::cerr << "[NIA-DOM] normalized constraints (" << normalized_.size() << "):\n";
        for (const auto& c : normalized_) {
            std::cerr << "  reason=" << c.reason.var << " rel=" << (int)c.rel
                      << " poly=" << kernel_->toString(c.poly) << "\n";
        }
    }

    // 4. Linear domain inference
    auto lr = linearDomain_.run(normalized_, domains_);
    if (lr.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*lr.conflict);
    }
    if (lr.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown("NIA: linear domain reasoning fatal unknown");
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }

    // 4.5 Product bound propagation: from a*b = c and a,b > 0 derive upper bounds
    for (const auto& c : normalized_) {
        if (c.rel != Relation::Eq) continue;
        auto termsOpt = kernel_->terms(c.poly);
        if (!termsOpt) {
            continue;
        }
        const auto& terms = *termsOpt;
        const PolynomialKernel::MonomialTerm* quadTerm = nullptr;
        const PolynomialKernel::MonomialTerm* constTerm = nullptr;
        for (const auto& t : terms) {
            if (t.powers.empty()) {
                constTerm = &t;
            } else if (t.powers.size() == 2 && t.powers[0].second == 1 && t.powers[1].second == 1) {
                quadTerm = &t;
            }
        }
        if (!quadTerm || !constTerm) {
            continue;
        }
        // Soundness: the product value x*y = -c0/cq is entailed only when the
        // equality is EXACTLY  cq*x*y + c0 = 0.  If any other term is present
        // (e.g. a*z in  x*y + a*z - 6 = 0), x*y is under-determined and a tight
        // upper bound from -c0/cq wrongly excludes valid solutions (false UNSAT).
        if (terms.size() != 2) {
            continue;
        }
        mpz_class numer = -constTerm->coefficient;
        mpz_class denom = quadTerm->coefficient;
        if (denom == 0) continue;
        if (numer % denom != 0) continue;
        mpz_class product = numer / denom;
        if (product <= 0) continue;

        std::string v1 = std::string(kernel_->varName(quadTerm->powers[0].first));
        std::string v2 = std::string(kernel_->varName(quadTerm->powers[1].first));
        const IntDomain* d1 = domains_.getDomain(v1);
        const IntDomain* d2 = domains_.getDomain(v2);
        if (!d1 || !d2) continue;
        if (!d1->hasLower || d1->lower.value <= 0) continue;
        if (!d2->hasLower || d2->lower.value <= 0) continue;

        mpz_class ub1 = product / d2->lower.value;
        mpz_class ub2 = product / d1->lower.value;
        domains_.addUpperBound(v1, ub1, c.reason);
        domains_.addUpperBound(v2, ub2, c.reason);
    }

    // 4.6 Propagate bounds through equalities (after product bounds)
    for (const auto& c : normalized_) {
        if (c.rel != Relation::Eq) continue;
        auto termsOpt = kernel_->terms(c.poly);
        if (!termsOpt) continue;
        const auto& terms = *termsOpt;
        const PolynomialKernel::MonomialTerm* constTerm = nullptr;
        std::vector<const PolynomialKernel::MonomialTerm*> varTerms;
        for (const auto& t : terms) {
            if (t.powers.empty()) {
                constTerm = &t;
            } else if (t.powers.size() == 1 && t.powers[0].second == 1) {
                varTerms.push_back(&t);
            } else {
                varTerms.clear();
                break;
            }
        }
        if (varTerms.size() != 2) continue;
        if (constTerm && constTerm->coefficient != 0) continue;
        const auto& t1 = *varTerms[0];
        const auto& t2 = *varTerms[1];
        if (t1.coefficient != -t2.coefficient) continue;

        std::string v1 = std::string(kernel_->varName(t1.powers[0].first));
        std::string v2 = std::string(kernel_->varName(t2.powers[0].first));
        const IntDomain* d1 = domains_.getDomain(v1);
        const IntDomain* d2 = domains_.getDomain(v2);
        if (!d1 && !d2) continue;

        // A bound propagated through the equality v1=v2 is justified by BOTH
        // the equality (c.reason) AND the source bound's own reasons. Dropping
        // the latter yields an over-strong (unsound) empty-domain conflict.
        auto withEq = [&](const std::vector<SatLit>& srcReasons) {
            std::vector<SatLit> rs = srcReasons;
            rs.push_back(c.reason);
            return rs;
        };
        auto propagate = [&](const std::string& src, const std::string& dst, const IntDomain* srcDom) {
            (void)src;
            if (!srcDom) return;
            if (srcDom->hasLower) domains_.addLowerBound(dst, srcDom->lower.value, withEq(srcDom->lower.reasons));
            if (srcDom->hasUpper) domains_.addUpperBound(dst, srcDom->upper.value, withEq(srcDom->upper.reasons));
        };

        if (d1 && !d2) propagate(v1, v2, d1);
        else if (!d1 && d2) propagate(v2, v1, d2);
        else if (d1 && d2) {
            if (d1->hasLower && (!d2->hasLower || d1->lower.value > d2->lower.value))
                domains_.addLowerBound(v2, d1->lower.value, withEq(d1->lower.reasons));
            if (d1->hasUpper && (!d2->hasUpper || d1->upper.value < d2->upper.value))
                domains_.addUpperBound(v2, d1->upper.value, withEq(d1->upper.reasons));
            if (d2->hasLower && (!d1->hasLower || d2->lower.value > d1->lower.value))
                domains_.addLowerBound(v1, d2->lower.value, withEq(d2->lower.reasons));
            if (d2->hasUpper && (!d1->hasUpper || d2->upper.value < d1->upper.value))
                domains_.addUpperBound(v1, d2->upper.value, withEq(d2->upper.reasons));
        }
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageSquareBound(TheoryLemmaStorage&, TheoryEffort) {
    auto sr = squareBound_.run(normalized_, domains_);
    if (sr.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*sr.conflict);
    }
    if (sr.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown("NIA: square bound reasoning fatal unknown");
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageSumOfSquares(TheoryLemmaStorage&, TheoryEffort) {
    auto ssr = sumOfSquaresBound_.run(normalized_, domains_);
    if (ssr.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*ssr.conflict);
    }
    if (ssr.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown("NIA: sum-of-squares bound reasoning fatal unknown");
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageUnivariate(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    auto ur = univariate_.run(normalized_, domains_, lemmaDb);
    if (ur.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*ur.conflict);
    }
    if (ur.kind == NiaReasoningKind::Lemma) {
        return TheoryCheckResult::mkLemma(*ur.lemma);
    }
    if (ur.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown("NIA: univariate reasoning fatal unknown");
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageAlgebraic(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    auto ar = algebraic_.run(normalized_, domains_, lemmaDb);
    if (ar.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*ar.conflict);
    }
    if (ar.kind == NiaReasoningKind::Lemma) {
        return TheoryCheckResult::mkLemma(*ar.lemma);
    }
    if (ar.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown("NIA: algebraic reasoning fatal unknown");
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageGcdDivisibility(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableGcd_) return std::nullopt;
    auto r = gcdDivisibility_.run(normalized_);
    if (r.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageModular(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableModular_) return std::nullopt;

    // L4.1 — modular warm-start memoization. The modular reasoner has
    // been profiled re-running its full detection (ModGroups, SimpleDefs,
    // CheckEqs, Newton-chain synthesis, Hensel lifting, residue
    // enumeration) every Full-effort cb_check on identical normalized_
    // streams. Skip the re-run when the constraint signature matches the
    // previous call's signature AND the previous result was NoChange.
    //
    // Soundness: NoChange writes no state and emits no verdict; replaying
    // it under unchanged signature is correctness-preserving. Conflicts
    // are NEVER memoized (the solver acts on a conflict by backtracking;
    // a stale conflict on a backtracked-from state would be unsound).
    //
    // Signature: FNV-1a over (poly, rel) pairs in normalized_ order —
    // same convention as the LS warm-start signature. Index order is
    // stable because normalized_ is grown in lockstep with active_ /
    // onBacktrack resizes it from the tail.
    static const bool warmStartEnabled = [] {
        return xolver::env::flag("XOLVER_NIA_MODULAR_WARM_START");
    }();
    auto computeSignature = [&]() -> uint64_t {
        uint64_t h = 1469598103934665603ULL;  // FNV-1a basis
        for (const auto& c : normalized_) {
            h ^= static_cast<uint64_t>(c.poly);
            h *= 1099511628211ULL;
            h ^= static_cast<uint64_t>(c.rel);
            h *= 1099511628211ULL;
        }
        return h;
    };
    if (warmStartEnabled && modularSignatureValid_ && modularLastWasNoChange_) {
        const uint64_t sig = computeSignature();
        if (sig == modularLastSignature_) {
            // Same constraint set, last verdict was NoChange — replay it.
            return std::nullopt;
        }
        // Signature changed: drop cache, fall through to re-run.
        modularSignatureValid_ = false;
    }

    auto r = modularResidue_.run(normalized_);
    if (r.kind == NiaReasoningKind::Conflict) {
        // Don't memoize conflicts (see soundness note above).
        modularSignatureValid_ = false;
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    // NoChange — cache signature for the next call.
    if (warmStartEnabled) {
        modularLastSignature_ = computeSignature();
        modularLastWasNoChange_ = true;
        modularSignatureValid_ = true;
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageNativeModEqConst(
    TheoryLemmaStorage&, TheoryEffort) {
    // Track A Phase 1.3 — bridge fact list to ModEqConstReasoner.
    static const bool enabled = [] {
        return xolver::env::flag("XOLVER_NIA_NATIVE_MODEQCONST");
    }();
    if (!enabled) return std::nullopt;
    if (modEqConstFacts_.empty()) return std::nullopt;
    if (!registry_) return std::nullopt;

    // Build a per-call snapshot of facts with `reason` resolved via the
    // TheoryAtomRegistry. Skip any fact whose atom is not currently asserted
    // true on the SAT trail.
    ModEqConstFactList active;
    active.reserve(modEqConstFacts_.size());
    for (const auto& src : modEqConstFacts_) {
        auto satVarOpt = registry_->findSatVarByExprId(src.atomExpr);
        if (!satVarOpt) continue;
        SatVar var = *satVarOpt;
        // Need positive polarity asserted (fact `(= (mod x y) c)` is true
        // only when the SAT layer has set the atom to true). The active
        // literal set tracks current-level asserted lits.
        SatLit posLit{var, /*sign=*/false};
        if (!activeSet_.contains(posLit)) continue;
        ModEqConstFact f = src;
        f.reason = posLit;
        active.push_back(std::move(f));
    }
    if (active.empty()) return std::nullopt;

    auto r = modEqConst_.run(active, domains_);
    if (r.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    // DomainUpdated / NoChange both fall through to the next stage.
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageProductPositivity(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableRefute_) return std::nullopt;
    auto r = productPositivity_.run(normalized_, domains_);
    if (r.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageInterval(TheoryLemmaStorage&, TheoryEffort) {
    // Interval evaluation (single-variable only, via common framework)
    ReasonedBox box;
    for (const auto& c : normalized_) {
        for (const auto& var : kernel_->variables(c.poly)) {
            if (box.get(var)) continue; // already set
            const IntDomain* d = domains_.getDomain(var);
            if (d && d->hasLower && d->hasUpper) {
                std::vector<SatLit> reasons;
                reasons.insert(reasons.end(), d->lower.reasons.begin(), d->lower.reasons.end());
                reasons.insert(reasons.end(), d->upper.reasons.begin(), d->upper.reasons.end());
                box.set(var, ReasonedInterval{IntervalZ{d->lower.value, d->upper.value}, reasons});
            }
        }
    }
    for (const auto& c : normalized_) {
        IntervalConstraint ic{c.poly, c.rel, c.reason};
        auto ir = intervalEvaluator_.run(ic, box);
        if (ir.status == IntervalEvalStatus::DefinitelyViolated) {
            std::vector<SatLit> lits;
            lits.push_back(c.reason);
            for (const auto& r : ir.usedReasons) {
                lits.push_back(r);
            }
            return TheoryCheckResult::mkConflict(TheoryConflict{lits});
        }
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

// Stage 3 Phase C-3 — NLA-cuts hook for NiaSolver. Mirrors the NraSolver
// hook (3eb2116) but operates on normalized_ (NormalizedNiaConstraint)
// and appends back into normalized_ so downstream stages see the cuts.
//
// Soundness:
//   Each cut is a logical implication of its source bounds — adding it to
//   normalized_ is sat/unsat preserving. The reason set must be a SINGLE
//   SatLit so it fits the NormalizedNiaConstraint shape (one reason per
//   constraint, matching the cacCons/activeReasons contract on the NRA
//   side); multi-reason cuts (monotonicityProduct, McCormick) are dropped
//   silently — they'd need a synthetic conjunction lit, pinned for the
//   next Phase D commit.
//
// The bound extraction handles c1*v + c0 rel 0 only (single var, degree 1,
// integer-constant c0/c1). Multi-var or nonlinear constraints are skipped.
std::optional<TheoryCheckResult> NiaSolver::stageNlaCuts(TheoryLemmaStorage&,
                                                          TheoryEffort) {
    static const bool nlaCutsEnabled = [] {
        return xolver::env::flag("XOLVER_NIA_NLA_CUTS");
    }();
    if (!nlaCutsEnabled) return std::nullopt;
    if (normalized_.empty()) return std::nullopt;

    std::map<VarId, nla::VarInterval> intervalMap;
    for (const auto& c : normalized_) {
        if (c.poly == NullPoly) continue;
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) continue;
        auto vars = rp->variables();
        if (vars.size() != 1) continue;
        VarId v = *vars.begin();
        if (rp->degree(v) != 1) continue;
        auto coeffs = rp->coefficients(v);
        if (coeffs.size() != 2) continue;
        if (!coeffs[0].isConstant() || !coeffs[1].isConstant()) continue;
        mpq_class c0 = coeffs[0].constantValue();
        mpq_class c1 = coeffs[1].constantValue();
        if (c1 == 0) continue;
        mpq_class bound = -c0 / c1;
        Relation effRel = c.rel;
        if (c1 < 0) {
            switch (effRel) {
                case Relation::Leq: effRel = Relation::Geq; break;
                case Relation::Geq: effRel = Relation::Leq; break;
                case Relation::Lt:  effRel = Relation::Gt;  break;
                case Relation::Gt:  effRel = Relation::Lt;  break;
                case Relation::Eq:  case Relation::Neq: break;
            }
        }
        auto& vi = intervalMap[v];
        if (vi.varPoly == NullPoly) vi.varPoly = kernel_->mkVar(v);
        auto tighter = [](std::optional<mpq_class>& lo,
                          std::optional<mpq_class>& hi,
                          const mpq_class& val, Relation r) {
            switch (r) {
                case Relation::Leq: case Relation::Lt:
                    if (!hi || val < *hi) hi = val;
                    break;
                case Relation::Geq: case Relation::Gt:
                    if (!lo || val > *lo) lo = val;
                    break;
                case Relation::Eq:
                    if (!lo || val > *lo) lo = val;
                    if (!hi || val < *hi) hi = val;
                    break;
                case Relation::Neq: break;
            }
        };
        tighter(vi.lo, vi.hi, bound, effRel);
        vi.reasons = {c.reason};
    }
    if (intervalMap.empty()) return std::nullopt;

    std::vector<nla::VarInterval> intervals;
    intervals.reserve(intervalMap.size());
    for (auto& [v, vi] : intervalMap) intervals.push_back(std::move(vi));

    nla::NlaCutsRunner runner(*kernel_);
    auto cuts = runner.runShapeCuts(intervals, /*maxPairs=*/0);
    for (const auto& cut : cuts) {
        if (cut.poly == NullPoly) continue;
        if (cut.reasons.size() != 1) continue;  // single-reason only
        // Append directly into normalized_. Subsequent stages see this as
        // any other NIA constraint; their cb_propagate path handles it.
        NormalizedNiaConstraint nc;
        nc.poly = cut.poly;
        nc.rel = cut.rel;
        nc.reason = cut.reasons[0];
        normalized_.push_back(nc);
    }
    return std::nullopt;
}

} // namespace xolver
