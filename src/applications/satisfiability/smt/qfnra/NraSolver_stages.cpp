#include "base/RuntimeConfig.h"
#include "applications/satisfiability/smt/qfnra/NraSolver.h"
#include "base/EnvParam.h"
#include "base/SolveClock.h"
#include <chrono>
#include "search/arith/Reasoner.h"
#include "algebra/linear/LinearExpr.h"
#include "search/presolve/Presolve.h"
#include "algebra/poly/RationalPolynomial.h"
#include "base/RealValue.h"                                // validated rational witness model
#include "search/nra/reasoners/SubtropicalSatFinder.h"  // subtropical candidate search
#include "search/nra/StructuralIntegerProbe.h"
#include "search/candidate/PartialLinearModelSearch.h"
#include "search/nra/NraSquareSolver.h"                   // algebraic square-cascade
#include "search/nra/core/HybridPartitionStats.h"     // Task NRA-HYB Step 1 partition stats
#include "search/nra/simplex/CertifiedSimplexFacts.h"   // OSF-CDCAC P1
#include "search/nra/simplex/NraLinearExtractor.h"      // §4.2 classifyConstraints
#include "search/nra/simplex/SimplexTableauFacts.h"     // §4.2 linearSubsetUnsat
#include "search/icp/IcpEngineQ.h"
#include "search/icp/ContractorFactoryQ.h"
#include "search/icp/IcpTypes.h"
#include "search/nra/core/CdcacCommon.h"                 // #63 relationHolds() for rational-fallback
#include "search/refute/SignDefinitenessRefuter.h"       // sign-definiteness refutation
#include "search/refute/PolynomialSignClosure.h"
#include "search/nra/core/CdcacCore.h"
#include "search/nra/core/CdcacConstraint.h"
#include "search/nra/engine/ReasonManager.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "search/nra/backend/LibpolyBackend.h"
#include "search/nra/reasoners/NlaCutsRunner.h"
#endif
#include <cstdlib>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <fstream>
#include <iostream>

namespace xolver {

// NOTE: This translation unit was split out of NraSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

std::optional<TheoryCheckResult> NraSolver::stagePartialLinearModel(
    TheoryLemmaStorage&, TheoryEffort) {
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty()) return std::nullopt;
    std::vector<PartialLinearModelSearch::Constraint> constraints;
    constraints.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) return std::nullopt;
        constraints.push_back({c.poly, c.rel});
    }
    PartialLinearModelSearch::Statistics stats;
    const auto started = std::chrono::steady_clock::now();
    auto model = PartialLinearModelSearch::trySolve(constraints, *kernel_, false, &stats);
    const auto profile = config::read<config::ReadKind::ProfilePath>("ARITH_STAGE_PROF", "/tmp/xolver_stageprof.txt");
    if (!profile.empty()) {
        std::ofstream out(profile.string() + ".boundary.log", std::ios::app);
        out << "variables=" << stats.variables << " parameters=" << stats.parameters
            << " retained_equalities=" << stats.retainedEqualityVariables
            << " contexts=" << stats.contexts << " checks=" << stats.linearChecks
            << " choices=" << stats.choices << " rejected=" << stats.rejectedChoices
            << " definitions=" << stats.definitions << " models=" << stats.modelChecks
            << " depth=" << stats.maxDepth << " exhausted=" << stats.exhausted
            << " found=" << bool(model) << " us="
            << std::chrono::duration_cast<std::chrono::microseconds>(
                   std::chrono::steady_clock::now() - started).count() << '\n';
    }
    if (!model) return std::nullopt;
    satFastModel_ = std::move(*model);
    return TheoryCheckResult::consistent();
}

// Stage 1: theory-check presolve fixpoint (Caps. 1–5, 7, with Real domain).
// May return a Conflict (UNSAT direction) via exact linear/sign reasoning,
// or a Lemma; it never returns SAT directly. nullopt → continue to CDCAC.
//
// Iter#22: per-call wall-clock deadline (parallels NIA's iter#21 deadline
// in stagePresolveFixpoint). Default 50 ms (XOLVER_NRA_PRESOLVE_BUDGET_MS;
// 0 disables). SOUND: the fixpoint's early-exit returns Progress/NoProgress
// based on the partial fact set already in st_.ledger — every recorded
// derivation is still semantically valid; downstream stages (CDCAC, ICP)
// see a SUBSET of what an unbounded run would derive, never an incorrect
// claim. Conflict / Lemma terminations always return immediately.
std::optional<TheoryCheckResult> NraSolver::stagePresolve(TheoryLemmaStorage& /*lemmaDb*/,
                                                          TheoryEffort /*effort*/) {
    const long presolveBudgetMs =
        config::read<config::ReadKind::Long>("XOLVER_NRA_PRESOLVE_BUDGET_MS", 50);
    PresolveEngine presolve(kernel_.get(), /*integerDomain=*/false);
    bool feasible = true;
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;  // non-polynomial placeholder
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) { feasible = false; break; }
        presolve.addAtom(*rp, c.rel, c.reason);
    }
    if (feasible) {
        auto deadline =
            (presolveBudgetMs > 0)
                ? std::chrono::steady_clock::now() +
                      std::chrono::milliseconds(presolveBudgetMs)
                : std::chrono::steady_clock::time_point::max();
        auto pr = presolve.run(deadline);
        if (pr.kind == PresolveResult::Kind::Conflict)
            return TheoryCheckResult::mkConflict(pr.conflict);
        if (pr.kind == PresolveResult::Kind::Lemma)
            return TheoryCheckResult::mkLemma(pr.lemma);
    }
    return std::nullopt;
}

// Each original model assigns a value to every monomial. Allowing these values
// to vary independently weakens the constraints, so a contradiction here is
// valid for the original polynomials. Unknown and feasible relaxations simply
// continue to the remaining stages; neither establishes nonlinear SAT.
std::optional<TheoryCheckResult> NraSolver::stageLinearRelaxation(
    TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort /*effort*/) {
    if (presolveConstraints_.empty()) return std::nullopt;

    // Skip unsupported placeholders; omitting a premise weakens the relaxation.
    std::vector<CdcacConstraint> cs;
    cs.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        CdcacConstraint cc;
        cc.poly = c.poly;
        cc.rel = c.rel;
        cc.reason = c.reason;
        cs.push_back(std::move(cc));
    }
    if (cs.empty()) return std::nullopt;

    auto relaxation = linearizeMonomials(*kernel_, cs);
    if (relaxation.empty()) return std::nullopt;

    auto facts = computeSimplexTableauFacts(relaxation);
    if (!facts.linearSubsetUnsat()) return std::nullopt;

    // Return active premises; TheoryManager negates them into the SAT clause.
    TheoryConflict conflict;
    conflict.clause = facts.conflictReasons();
    if (conflict.clause.empty())
        for (const auto& la : relaxation) conflict.clause.push_back(la.reason);
    if (conflict.clause.empty()) return std::nullopt;
    return TheoryCheckResult::mkConflict(std::move(conflict));
}

// Step 2.1: GLOBAL box-consistency refutation, run EARLY (before the covering
// engines). The box-ICP (incl. degree-2 square contraction) over all of ℝⁿ decides
// bound-contradiction families — most importantly the hong family (Σx²<1 ⇒ |x_i|<1
// ⇒ |Πx|<1, contra Πx>1) — in ~ms. Without this the conflict is only found by the
// CdcacCore box-check INSIDE stageCdcac, i.e. AFTER stageCac has already spent a 10s+
// covering blowup on the same problem (measured: hong_8 cac=10.76s). Running it up
// front short-circuits that. Sound: interval over-approximation, empty box ⇒ UNSAT.
// Skips combination mode (interface (dis)eqs live in engine_, not the box).
std::optional<TheoryCheckResult> NraSolver::stageBoxRefute(TheoryLemmaStorage& /*lemmaDb*/,
                                                           TheoryEffort /*effort*/) {
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;
    std::vector<SatLit> reasons;
    if (!engine_.globalBoxRefute(reasons)) return std::nullopt;
    return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
}

// Positive-orthant sign-definiteness refuter. Cheap,
// unconditionally sound UNSAT for sign-definite constraints (e.g. a sum of
// strictly-positive monomials = 0 with all variables positive — the Sturm-MBO
// family that CAD/CAC time out on).
std::optional<TheoryCheckResult> NraSolver::stageSignRefute(TheoryLemmaStorage& /*lemmaDb*/,
                                                            TheoryEffort effort) {
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;   // combination: interface (dis)eqs not in presolveConstraints_

    std::vector<SignRefuteConstraint> cs;
    cs.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) continue;     // skip unrepresentable; a missing constraint only loses completeness
        cs.push_back({std::move(*rp), c.rel, c.reason});
    }
    auto conflict = refuteBySignDefiniteness(cs);
    if (!conflict && effort == TheoryEffort::Full) {
        PolynomialSignStatistics stats;
        const auto started = std::chrono::steady_clock::now();
        conflict = refuteByPolynomialSignClosure(cs, &stats);
        const auto profile = config::read<config::ReadKind::ProfilePath>("ARITH_STAGE_PROF", "/tmp/xolver_stageprof.txt");
        if (!profile.empty()) {
            std::ofstream out(profile.string() + ".polynomial-sign.log", std::ios::app);
            out << "rounds=" << stats.rounds << " facts=" << stats.inferredFacts
                << " substitutions=" << stats.substitutions << " cancellations=" << stats.cancellations
                << " divisions=" << stats.divisions << " conflict=" << bool(conflict)
                << " exhausted=" << stats.exhausted << " us="
                << std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now() - started).count() << '\n';
        }
    }
    if (!conflict && effort == TheoryEffort::Full) {
        QuadraticSignStatistics stats;
        const auto started = std::chrono::steady_clock::now();
        conflict = refuteByQuadraticSigns(cs, &stats);
        const auto profile = config::read<config::ReadKind::ProfilePath>("ARITH_STAGE_PROF", "/tmp/xolver_stageprof.txt");
        if (!profile.empty()) {
            std::ofstream out(profile.string() + ".quadratic-sign.log", std::ios::app);
            out << "attempts=" << stats.quadraticAttempts << " divisions=" << stats.factorDivisions
                << " certified=" << stats.certified << " exhausted=" << stats.exhausted
                << " us=" << std::chrono::duration_cast<std::chrono::microseconds>(
                    std::chrono::steady_clock::now() - started).count() << '\n';
        }
    }
    if (!conflict) return std::nullopt;

    TheoryConflict tc;
    tc.clause = std::move(*conflict);
    if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NRA_SIGN_REFUTE_DIAG")) {
        std::ofstream st("/tmp/sign_refute.txt", std::ios::app);
        st << "[SIGN-REFUTE] UNSAT cons=" << cs.size() << " clause=" << tc.clause.size() << "\n";
        st.flush();
    }
    return TheoryCheckResult::mkConflict(std::move(tc));
}

// Subtropical candidate search. A cheap, incomplete
// witness search "at infinity" run before the full CAD. It produces a CANDIDATE
// assignment; every active original constraint is then exact-validated via the
// kernel sign (invariant 1). SAT only on a validated model (stored in
// satFastModel_ so getModel() reports it); otherwise nullopt → fall to CDCAC.
std::optional<TheoryCheckResult> NraSolver::stageSubtropical(TheoryLemmaStorage& /*lemmaDb*/,
                                                             TheoryEffort effort) {
    if (effort != TheoryEffort::Full) return std::nullopt;  // fast path at full effort only
    // Combination (Nelson-Oppen) mode: interface (dis)equalities live in the
    // engine, not presolveConstraints_, so a witness validated only against the
    // local atoms could violate them. Restrict the fast path to pure NRA.
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;

    // --- Build the subtropical constraint set from the active polynomials. ---
    // Bail (fall through) if ANY active constraint is non-polynomial or cannot be
    // decomposed into integer-coefficient terms: a witness validated only against
    // a SUBSET would be unsound to report as SAT.
    std::vector<SubtropicalConstraint> subCons;
    std::unordered_set<VarId> varSet;
    subCons.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) return std::nullopt;
        auto termsOpt = kernel_->terms(c.poly);
        if (!termsOpt) return std::nullopt;
        SubtropicalConstraint sc;
        sc.rel = c.rel;
        sc.monomials.reserve(termsOpt->size());
        for (const auto& t : *termsOpt) {
            if (t.coefficient == 0) continue;
            SubtropicalMonomial m;
            m.coeff = t.coefficient;
            m.powers = t.powers;
            for (const auto& pr : t.powers) varSet.insert(pr.first);
            sc.monomials.push_back(std::move(m));
        }
        subCons.push_back(std::move(sc));
    }
    if (subCons.empty() || varSet.empty()) return std::nullopt;  // ground / nothing to do

    std::vector<VarId> vars(varSet.begin(), varSet.end());

    SubtropicalSatFinder finder;
    SubtropicalSatFinder::Statistics stats;
    const auto started = std::chrono::steady_clock::now();
    SubtropicalResult r = finder.find(subCons, vars, &stats);
    const auto profile = config::read<config::ReadKind::ProfilePath>("ARITH_STAGE_PROF", "/tmp/xolver_stageprof.txt");
    if (!profile.empty()) {
        std::ofstream out(profile.string() + ".subtropical.log", std::ios::app);
        out << "variables=" << vars.size() << " constraints=" << subCons.size()
            << " contexts=" << stats.contexts << " nodes=" << stats.nodes
            << " frames=" << stats.frames << " definitions=" << stats.definitions
            << " reused_rows=" << stats.reusedRows << " checks=" << stats.linearChecks
            << " parity_conflicts=" << stats.parityConflicts << " backtracks=" << stats.backtracks
            << " exhausted=" << stats.exhausted << " found=" << r.found << " us="
            << std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - started).count() << '\n';
    }
    if (!r.found) return std::nullopt;

    // Guard against pathological magnitudes (base^exp blow-up). Sound to skip.
    for (const auto& [v, e] : r.dir.exponents) {
        if (abs(e) > 64) return std::nullopt;
    }

    // --- Materialize over increasing bases and exact-validate (invariant 1). -
    static const long kBases[] = {2, 4, 16, 256, 4096, 65536};
    for (long b : kBases) {
        auto vidModel = SubtropicalSatFinder::materialize(r.dir, vars, mpq_class(b));
        std::unordered_map<std::string, mpq_class> model;
        model.reserve(vidModel.size());
        for (const auto& [v, val] : vidModel) model.emplace(std::string(kernel_->varName(v)), val);

        bool allHold = true;
        for (const auto& c : presolveConstraints_) {
            std::unordered_map<std::string, mpq_class> evalModel = model;
            for (const auto& vn : kernel_->variables(c.poly))
                evalModel.emplace(vn, mpq_class(0));  // 0-fill (defensive)
            const int s = kernel_->sgn(c.poly, evalModel);
            bool ok = false;
            switch (c.rel) {
                case Relation::Eq:  ok = (s == 0); break;
                case Relation::Geq: ok = (s >= 0); break;
                case Relation::Leq: ok = (s <= 0); break;
                case Relation::Gt:  ok = (s > 0);  break;
                case Relation::Lt:  ok = (s < 0);  break;
                case Relation::Neq: ok = (s != 0); break;
            }
            if (!ok) { allHold = false; break; }
        }
        if (allHold) {
            // Sound: a concrete rational point validates ALL active constraints
            // under the exact kernel sign. Stash it so getModel() reports it.
            satFastModel_ = std::move(vidModel);
            if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NRA_SUBTROP_DIAG")) {
                std::ofstream st("/tmp/subtropical.txt", std::ios::app);
                st << "[SUBTROP] SAT vars=" << vars.size()
                   << " cons=" << subCons.size() << " base=" << b << "\n";
                st.flush();
            }
            return TheoryCheckResult::consistent();
        }
    }
    return std::nullopt;  // no base validated: fall through to CDCAC
}

// Equality-cascade SAT solver (mgc-class). Assign the
// high-degree generator variables, which collapses every high-degree monomial
// (vv3^16, …) to a number and turns each residual equality linear; derive the
// remaining variables (gamma0, vv2, lambda1, mu, …) and validate the full point
// exactly via the kernel sign over ALL active constraints (invariant 1). Pure
// rational throughout — never libpoly root isolation — so it closes mgc_09/10
// where CDCAC times out projecting the degree-16/18 atom. Pure-NRA only;
// combination/N-O mode falls through (interface (dis)equalities live outside
// presolveConstraints_). SAT-only: no model found ⇒ nullopt ⇒ CDCAC/Unknown.
std::optional<TheoryCheckResult> NraSolver::stageCascade(
        TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort effort) {
    (void)effort;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;
    if (presolveConstraints_.empty()) return std::nullopt;

    std::vector<StructuralIntegerProbe::Constraint> cons;
    cons.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) return std::nullopt;
        cons.push_back({c.poly, c.rel});
    }

    auto modelOpt = StructuralIntegerProbe::trySolveCascade(cons, *kernel_);
    if (!modelOpt) return std::nullopt;
    satFastModel_ = std::move(*modelOpt);
    return TheoryCheckResult::consistent();
}

// Algebraic square-cascade builds
// and EXACT-validates a Q(sqrt c) model for square-defined systems the rational
// eq-cascade can't (v^2 = non-square => algebraic root). Sound by construction:
// trySquareCascade returns true only after checking every original constraint's exact
// sign at the constructed model (invariant 1); on any inconclusive/failing check it
// returns false and we fall through to CAC/Collins unchanged.
std::optional<TheoryCheckResult> NraSolver::stageSquareCascade(
        TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort /*effort*/) {
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty()) return std::nullopt;
    if (presolveConstraints_.empty()) return std::nullopt;

    std::vector<std::pair<PolyId, Relation>> cons;
    cons.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) return std::nullopt;
        cons.emplace_back(c.poly, c.rel);
    }
    std::vector<std::pair<VarId, RealValue>> model;
    if (!trySquareCascade(cons, *kernel_, &model)) return std::nullopt;
    satCacAlgModel_ = std::move(model);
    return TheoryCheckResult::consistent();
}

} // namespace xolver
