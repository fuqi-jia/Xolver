#include "theory/arith/logics/nra/NraSolver.h"
#include "util/EnvParam.h"
#include "util/SolveClock.h"
#include <chrono>
#include "theory/arith/Reasoner.h"
#include "theory/arith/kernel/linear/LinearExpr.h"
#include "theory/arith/kernel/presolve/Presolve.h"
#include "theory/arith/kernel/poly/RationalPolynomial.h"
#include "util/RealValue.h"                                // XOLVER_NRA_SUBTROPICAL witness model
#include "theory/arith/logics/nra/NraLinearizationAdapter.h"     // XOLVER_NRA_LINEARIZE cut-feeder
#include "theory/arith/logics/nia/preprocess/NiaNormalizer.h"    // XOLVER_NRA_LINEARIZE: normalize nonlinear cstrs
#include "theory/arith/logics/nra/reasoners/SubtropicalSatFinder.h"  // XOLVER_NRA_SUBTROPICAL SAT-fast-path
#include "theory/arith/logics/nra/StructuralIntegerProbe.h"          // XOLVER_NRA_INT_PROBE
#include "theory/arith/logics/nra/NraSquareSolver.h"                   // algebraic square-cascade
#include "theory/arith/logics/nra/reasoners/NraLocalSearch.h"        // XOLVER_NRA_LOCALSEARCH Phase NRA-LS-A
#include "theory/arith/logics/nra/core/HybridPartitionStats.h"     // Task NRA-HYB Step 1 partition stats
#include "theory/arith/logics/nra/simplex/CertifiedSimplexFacts.h"   // OSF-CDCAC P1
#include "theory/arith/logics/nra/simplex/NraLinearExtractor.h"      // §4.2 classifyConstraints
#include "theory/arith/logics/nra/simplex/SimplexTableauFacts.h"     // §4.2 linearSubsetUnsat
#include "theory/arith/logics/nra/simplex/PolynomialIntervalPruner.h" // OSF-CDCAC P7
#include "theory/arith/kernel/icp/IcpEngineQ.h"                       // XOLVER_NRA_ICP rational ICP engine
#include "theory/arith/kernel/icp/ContractorFactoryQ.h"               // XOLVER_NRA_ICP factory
#include "theory/arith/kernel/icp/IcpTypes.h"                         // XOLVER_NRA_ICP IcpConstraint
#include "theory/arith/logics/nra/cac/CacEngine.h"                    // XOLVER_NRA_CAC conflict-driven coverings
#include "theory/arith/logics/nra/core/CdcacCommon.h"                 // #63 relationHolds() for rational-fallback
#include "theory/arith/kernel/refute/SignDefinitenessRefuter.h"       // XOLVER_NRA_SIGN_REFUTE
#include "theory/arith/logics/nra/core/CdcacCore.h"               // XOLVER_NRA_PREELIM reduced CDCAC
#include "theory/arith/logics/nra/core/CdcacConstraint.h"         // XOLVER_NRA_PREELIM
#include "theory/arith/logics/nra/engine/ReasonManager.h"         // XOLVER_NRA_PREELIM conflict reasons
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/logics/nra/backend/LibpolyBackend.h"       // XOLVER_NRA_PREELIM algebra backend
#include "theory/arith/logics/nra/reasoners/NlaCutsRunner.h"             // XOLVER_NRA_NLA_CUTS Phase C-2 hook
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
    static const long presolveBudgetMs =
        env::paramLong("XOLVER_NRA_PRESOLVE_BUDGET_MS", 50);
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

// §4.2 linear-subset UNSAT pre-check.
//
// Reads presolveConstraints_, classifies them into linear and nonlinear,
// and runs SimplexTableauFacts on the linear subset. If the linear
// subset alone is infeasible, the full NRA query is infeasible — the
// linear contradiction is a sound theory conflict witnessed entirely by
// original active SAT literals.
//
// The conflict clause includes the SAT literals of EVERY linear atom
// (a non-minimal Farkas witness). Sound: the clause `OR ¬lit_i` is
// theory-valid because the conjunction of all linear atoms is UNSAT,
// so at least one lit_i must be false in any model.
//
// Default-OFF — opt-in via XOLVER_NRA_LINEAR_SUBSET_UNSAT=1 until a
// production validation pass measures the perf impact (the simplex runs
// per cb_propagate when enabled).
std::optional<TheoryCheckResult> NraSolver::stageLinearSubsetUnsat(
    TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort /*effort*/) {
    static const bool enabled = [] {
        return xolver::env::flag("XOLVER_NRA_LINEAR_SUBSET_UNSAT");
    }();
    if (!enabled) return std::nullopt;
    if (presolveConstraints_.empty()) return std::nullopt;

    // Build a CdcacConstraint view (skip placeholders). NraSolver's
    // PresolveCstr carries the same {poly, rel, reason} triple — copy
    // the live entries into the shape classifyConstraints wants.
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

    auto classified = classifyConstraints(*kernel_, cs);
    if (classified.linear.empty()) return std::nullopt;

    auto facts = computeSimplexTableauFacts(*kernel_, classified.linear);
    if (!facts.linearSubsetUnsat()) return std::nullopt;

    // Sound conflict: union all linear-atom SAT lits. At least one must
    // be false in any model since their conjunction is UNSAT.
    TheoryConflict conflict;
    conflict.clause.reserve(classified.linear.size());
    for (const auto& la : classified.linear) {
        conflict.clause.push_back(la.reason);
    }
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

// XOLVER_NRA_ICP: rational ICP probe. Sound by construction — emits Conflict
// only when a contractor reports a definitively-violated constraint with
// reasons that union the constraint's reason and the box's bound reasons.
// V1 scope: univariate atoms only. Linear single-var bounds seed the box;
// degree-≥2 single-var polynomials run through RelationContractorQ. Bypassed
// in combination mode (interface (dis)eqs not in presolveConstraints_, matches
// sign-refute's bailout).
std::optional<TheoryCheckResult> NraSolver::stageIcpProbe(TheoryLemmaStorage& /*lemmaDb*/,
                                                          TheoryEffort /*effort*/) {
    static const bool enabled = [] {
        return xolver::env::flag("XOLVER_NRA_ICP");
    }();
    if (!enabled) return std::nullopt;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;

    // Pass 1: seed partial bounds from univariate linear atoms.
    // Closed-interval over-approximation for strict atoms is sound — it only
    // weakens conflict detection, never adds spurious conflicts.
    struct PartialBound {
        bool hasLo = false; mpq_class lo;
        bool hasHi = false; mpq_class hi;
        std::vector<SatLit> reasonsLo;
        std::vector<SatLit> reasonsHi;
    };
    std::unordered_map<std::string, PartialBound> partial;

    auto narrowLo = [&partial](const std::string& v, const mpq_class& val, SatLit r) {
        auto& pb = partial[v];
        if (!pb.hasLo || val > pb.lo) {
            pb.lo = val; pb.reasonsLo.clear();
        }
        if (!pb.hasLo || val >= pb.lo) {
            pb.reasonsLo.push_back(r);
        }
        pb.hasLo = true;
    };
    auto narrowHi = [&partial](const std::string& v, const mpq_class& val, SatLit r) {
        auto& pb = partial[v];
        if (!pb.hasHi || val < pb.hi) {
            pb.hi = val; pb.reasonsHi.clear();
        }
        if (!pb.hasHi || val <= pb.hi) {
            pb.reasonsHi.push_back(r);
        }
        pb.hasHi = true;
    };

    std::vector<IcpConstraint> nonlinearAtoms;
    nonlinearAtoms.reserve(presolveConstraints_.size());

    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        auto vars = kernel_->variables(c.poly);

        if (vars.size() >= 2) {
            // Multivariate: feed to V4 (the factory will discard non-V4
            // shapes). No bound-seeding — V4 reads the rest-vars' boxes
            // populated by the univariate linear pass.
            IcpConstraint ic;
            ic.expr = std::nullopt;
            ic.poly = c.poly;
            ic.rel = c.rel;
            ic.reason = c.reason;
            ic.owner = TheoryId::NRA;
            nonlinearAtoms.push_back(ic);
            continue;
        }
        if (vars.size() != 1) continue;  // 0 vars (constant): handled by presolve

        const std::string& v = vars[0];
        auto degOpt = kernel_->degree(c.poly, v);
        if (!degOpt) continue;

        if (*degOpt == 1) {
            // Linear: c1*x + c0 rel 0  ⇒  bound on x.
            auto coeffsOpt = kernel_->getIntegerCoefficients(c.poly, v);
            if (!coeffsOpt || coeffsOpt->size() != 2) continue;
            const mpz_class& c1 = (*coeffsOpt)[0];
            const mpz_class& c0 = (*coeffsOpt)[1];
            if (c1 == 0) continue;  // shouldn't happen at degree 1, defense-in-depth

            mpq_class bound(-c0, c1);
            bound.canonicalize();
            bool flip = (c1 < 0);

            // After flip, work in the canonical c1>0 frame.
            Relation rel = c.rel;
            switch (rel) {
                case Relation::Eq:
                    narrowLo(v, bound, c.reason);
                    narrowHi(v, bound, c.reason);
                    break;
                case Relation::Leq:
                    if (flip) narrowLo(v, bound, c.reason);
                    else      narrowHi(v, bound, c.reason);
                    break;
                case Relation::Geq:
                    if (flip) narrowHi(v, bound, c.reason);
                    else      narrowLo(v, bound, c.reason);
                    break;
                case Relation::Lt:
                    // Strict over-approximated to non-strict (sound: feasible
                    // set ⊆ closed-interval). No precision loss for sound
                    // conflict detection.
                    if (flip) narrowLo(v, bound, c.reason);
                    else      narrowHi(v, bound, c.reason);
                    break;
                case Relation::Gt:
                    if (flip) narrowHi(v, bound, c.reason);
                    else      narrowLo(v, bound, c.reason);
                    break;
                case Relation::Neq:
                default:
                    break;  // V1: skip (would need disjunctive narrowing)
            }
        } else if (*degOpt >= 2) {
            // Univariate degree ≥ 2 — gather for contractor pass.
            IcpConstraint ic;
            ic.expr = std::nullopt;
            ic.poly = c.poly;
            ic.rel = c.rel;
            ic.reason = c.reason;
            ic.owner = TheoryId::NRA;
            nonlinearAtoms.push_back(ic);
        }
    }

    // Pass 2: build the box only from variables with BOTH endpoints — no
    // infinity sentinel exists in IntervalQ, so a half-bounded var is unsafe
    // for interval polynomial evaluation (would need ±∞ propagation rules).
    ReasonedBoxQ box;
    for (auto& [v, pb] : partial) {
        if (!pb.hasLo || !pb.hasHi) continue;
        if (pb.lo > pb.hi) {
            // Linear seeds alone already proved infeasibility on x — emit the
            // direct conflict; presolve normally catches this too, this is
            // defense-in-depth so ICP never runs over an empty box.
            std::vector<SatLit> reasons = pb.reasonsLo;
            reasons.insert(reasons.end(), pb.reasonsHi.begin(), pb.reasonsHi.end());
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
        }
        std::vector<SatLit> reasons = pb.reasonsLo;
        reasons.insert(reasons.end(), pb.reasonsHi.begin(), pb.reasonsHi.end());
        box.set(v, ReasonedIntervalQ{IntervalQ{pb.lo, pb.hi}, std::move(reasons)});
    }

    // Without any seeded variable, no contractor can fire. Skip the engine.
    if (box.entries().empty()) return std::nullopt;
    if (nonlinearAtoms.empty()) return std::nullopt;

    auto built = ContractorFactoryQ::build(nonlinearAtoms, *kernel_);
    if (built.contractors.empty()) return std::nullopt;

    IcpConfig cfg;  // defaults are fine; budget keeps the worklist bounded
    IcpEngineQ engine;
    auto r = engine.run(built.contractors, built.watchers, box, cfg);
    if (r.status == IcpStatus::Conflict && r.conflict) {
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    return std::nullopt;
}

// XOLVER_NRA_SIGN_REFUTE: positive-orthant sign-definiteness refuter. Cheap,
// unconditionally sound UNSAT for sign-definite constraints (e.g. a sum of
// strictly-positive monomials = 0 with all variables positive — the Sturm-MBO
// family that CAD/CAC time out on).
std::optional<TheoryCheckResult> NraSolver::stageSignRefute(TheoryLemmaStorage& /*lemmaDb*/,
                                                            TheoryEffort /*effort*/) {
    if (!enableSignRefute_) return std::nullopt;
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
    if (!conflict) return std::nullopt;

    TheoryConflict tc;
    tc.clause = std::move(*conflict);
    if (xolver::env::diag("XOLVER_NRA_SIGN_REFUTE_DIAG")) {
        std::ofstream st("/tmp/sign_refute.txt", std::ios::app);
        st << "[SIGN-REFUTE] UNSAT cons=" << cs.size() << " clause=" << tc.clause.size() << "\n";
        st.flush();
    }
    return TheoryCheckResult::mkConflict(std::move(tc));
}

// nra.groebner — cross-equation ideal-saturation refutation. Reuses the
// (theory-agnostic) GroebnerIdealReasoner on the asserted EQUALITY polynomials:
// a degree/step-bounded Buchberger reduction; if 1 ∈ ideal(equalities) the system
// has no common root over ℂ, hence none over ℝ ⇒ UNSAT. SOUND: presolveConstraints_
// is the live asserted set (truncated on backtrack, like stageSignRefute), so every
// reason in the emitted conflict is currently on the trail. Bounded (the reasoner
// bails to NoChange past its budget). Catches cross-equation obstructions (e.g.
// x*y=1 ∧ x=0) that sign-refute / single-substitution miss.
std::optional<TheoryCheckResult> NraSolver::stageGroebner(TheoryLemmaStorage& /*lemmaDb*/,
                                                          TheoryEffort /*effort*/) {
    if (!enableGroebner_) return std::nullopt;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;   // combination: interface (dis)eqs not in presolveConstraints_

    std::vector<NormalizedNiaConstraint> cs;
    cs.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        cs.push_back({c.poly, c.rel, c.reason});   // reasoner filters to equalities internally
    }
    if (cs.size() < 2) return std::nullopt;

    // Warm-start dedup: the bounded Buchberger run is non-trivial, and the SAT search
    // re-enters check() many times with an UNCHANGED constraint set. Skip the re-run
    // when the (poly,rel) signature matches the last NO-CONFLICT call. Sound: replaying
    // a no-conflict verdict is safe; a hash collision only loses completeness (we fall
    // through to CDCAC), never soundness.
    size_t sig = 1469598103934665603ull;   // FNV-1a over (poly,rel)
    for (const auto& c : cs) {
        sig = (sig ^ static_cast<size_t>(c.poly)) * 1099511628211ull;
        sig = (sig ^ static_cast<size_t>(c.rel)) * 1099511628211ull;
    }
    if (groebnerNoConflictSig_ == sig) return std::nullopt;

    auto r = groebner_.run(cs);
    if (r.kind != NiaReasoningKind::Conflict || !r.conflict) groebnerNoConflictSig_ = sig;
    if (r.kind == NiaReasoningKind::Conflict && r.conflict) {
        if (xolver::env::diag("XOLVER_NRA_GROBNER_DIAG"))
            std::fprintf(stderr, "[NRA-GROBNER] UNSAT cons=%zu\n", cs.size());
        return TheoryCheckResult::mkConflict(std::move(*r.conflict));
    }
    return std::nullopt;
}

// XOLVER_NRA_SIGN_SPLIT (default OFF). MGC-RD closing lever.
//
// When sign-refute fails because exactly ONE variable's sign is unknown in
// an otherwise-refutable equation/inequality, emit a 3-way case-split
// theory lemma  (or (> v 0) (= v 0) (< v 0))  on that variable. The
// disjunction is a tautology over R (covers every real number), so adding
// it never alters the feasible region — soundness is structural. In each
// branch the variable's sign becomes definite, sign-refute fires.
//
// Per-solve dedup via signSplitDone_; cleared in onReset to enable a fresh
// split set per solve.
std::optional<TheoryCheckResult> NraSolver::stageNraSignSplit(
        TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort /*effort*/) {
    static const bool enabled = []() {
        const char* e = std::getenv("XOLVER_NRA_SIGN_SPLIT");
        return e && *e && *e != '0';
    }();
    if (!enabled) return std::nullopt;
    // Run at every effort: the lemma is a tautology so emitting early
    // (Standard effort) lets SAT branch before propagation digs deep.
    if (!registry_) return std::nullopt;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;
    if (presolveConstraints_.empty()) return std::nullopt;

    // Pass 1: derive known signs from single-var linear bounds (mirrors
    // SignDefinitenessRefuter so we agree on which vars are unknown).
    enum class Sign : uint8_t { Unknown, PosStrict, NegStrict, NonNeg, NonPos };
    std::unordered_map<VarId, Sign> known;
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        auto rpOpt = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rpOpt) continue;
        const auto& rp = *rpOpt;
        const auto vars = rp.variables();
        if (vars.size() != 1) continue;
        const VarId v = *vars.begin();
        if (rp.degree(v) != 1) continue;
        mpq_class coeff = 0, constTerm = 0;
        for (const auto& [mon, k] : rp.terms()) {
            if (mon.empty()) constTerm = k;
            else if (mon.size() == 1 && mon[0].first == v && mon[0].second == 1) coeff = k;
            else { coeff = 0; break; }
        }
        if (coeff == 0) continue;
        mpq_class boundary = -constTerm / coeff;
        Relation rel = c.rel;
        if (coeff < 0) {
            switch (rel) {
                case Relation::Lt:  rel = Relation::Gt; break;
                case Relation::Leq: rel = Relation::Geq; break;
                case Relation::Gt:  rel = Relation::Lt;  break;
                case Relation::Geq: rel = Relation::Leq; break;
                default: break;
            }
        }
        Sign s = Sign::Unknown;
        if (rel == Relation::Gt && boundary >= 0) s = Sign::PosStrict;
        else if (rel == Relation::Geq && boundary > 0) s = Sign::PosStrict;
        else if (rel == Relation::Geq && boundary == 0) s = Sign::NonNeg;
        else if (rel == Relation::Lt && boundary <= 0) s = Sign::NegStrict;
        else if (rel == Relation::Leq && boundary < 0) s = Sign::NegStrict;
        else if (rel == Relation::Leq && boundary == 0) s = Sign::NonPos;
        if (s == Sign::Unknown) continue;
        auto& slot = known[v];
        // Strict wins over non-strict.
        if (slot == Sign::Unknown ||
            ((s == Sign::PosStrict || s == Sign::NegStrict) &&
             !(slot == Sign::PosStrict || slot == Sign::NegStrict))) {
            slot = s;
        }
    }

    // Pass 2: find a sign-blocking variable. Heuristic: pick the unknown-sign
    // variable that appears in the most constraints. Only consider vars that
    // haven't been split before this solve.
    std::unordered_map<VarId, int> unknownVarUseCount;
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        for (const auto& vn : kernel_->variables(c.poly)) {
            auto vid = kernel_->findVar(vn);
            if (!vid) continue;
            if (known.find(*vid) != known.end()) continue;
            if (signSplitDone_.count(*vid)) continue;
            unknownVarUseCount[*vid]++;
        }
    }
    if (unknownVarUseCount.empty()) return std::nullopt;
    VarId pick = NullVar;
    int bestCount = 0;
    for (const auto& [v, n] : unknownVarUseCount) {
        if (n > bestCount) { pick = v; bestCount = n; }
    }
    if (pick == NullVar) return std::nullopt;

    // Emit the 3-way disjunction lemma: (or (> v 0) (= v 0) (< v 0)).
    // Each atom is on (v - 0), i.e. just the poly v.
    PolyId vPoly = kernel_->mkVar(pick);
    SatLit gt = registry_->getOrCreatePolynomialAtom(vPoly, Relation::Gt, mpq_class(0), TheoryId::LRA);
    SatLit eq = registry_->getOrCreatePolynomialAtom(vPoly, Relation::Eq, mpq_class(0), TheoryId::LRA);
    SatLit lt = registry_->getOrCreatePolynomialAtom(vPoly, Relation::Lt, mpq_class(0), TheoryId::LRA);
    if (gt.var == 0 || eq.var == 0 || lt.var == 0) return std::nullopt;

    TheoryLemma lemma{{gt, eq, lt}};
    signSplitDone_.insert(pick);

    if (xolver::env::diag("XOLVER_NRA_SIGN_SPLIT_DIAG")) {
        std::fprintf(stderr,
            "[XOLVER_NRA_SIGN_SPLIT] split on var=%u uses=%d  lemma=(>0 | =0 | <0)\n",
            (unsigned)pick, bestCount);
    }
    return TheoryCheckResult::mkLemma(std::move(lemma));
}

// OSF-CDCAC P7: stageOsfPrune.
//
// Build a CertifiedSimplexFacts from the active single-variable linear
// bounds in presolveConstraints_. Then run polynomial interval pruning:
// for each constraint p rel 0, compute [L, U] via monomial arithmetic.
// If the interval contradicts rel, emit a sound theory conflict.
//
// Distinct from SignDefinitenessRefuter: that one only tracks SIGN
// (Pos/Neg/NonNeg/NonPos), this tracks NUMERIC bounds so constraints
// like x in [2,5] and y in [3,4] propagate through x*y to [6, 20].
//
// Default OFF until paired-validated on broader corpus.
std::optional<TheoryCheckResult> NraSolver::stageOsfPrune(
        TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort /*effort*/) {
    static const bool enabled = []() {
        return xolver::env::flag("XOLVER_NRA_OSF_PRUNE");
    }();
    if (!enabled) return std::nullopt;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;
    if (presolveConstraints_.empty()) return std::nullopt;

    // Build CertifiedSimplexFacts from single-variable linear constraints.
    CertifiedSimplexFacts facts;
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        auto rpOpt = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rpOpt) continue;
        const auto& rp = *rpOpt;
        const auto vars = rp.variables();
        if (vars.size() != 1) continue;
        const VarId v = *vars.begin();
        if (rp.degree(v) != 1) continue;
        mpq_class coeff = 0, constTerm = 0;
        for (const auto& [mon, k] : rp.terms()) {
            if (mon.empty()) constTerm = k;
            else if (mon.size() == 1 && mon[0].first == v && mon[0].second == 1) coeff = k;
            else { coeff = 0; break; }
        }
        if (coeff == 0) continue;
        mpq_class boundary = -constTerm / coeff;
        Relation rel = c.rel;
        if (coeff < 0) {
            switch (rel) {
                case Relation::Lt:  rel = Relation::Gt;  break;
                case Relation::Leq: rel = Relation::Geq; break;
                case Relation::Gt:  rel = Relation::Lt;  break;
                case Relation::Geq: rel = Relation::Leq; break;
                default: break;
            }
        }
        std::vector<SatLit> reasons{c.reason};
        switch (rel) {
            case Relation::Gt:  facts.tightenLower(v, boundary, /*strict=*/true,  reasons); break;
            case Relation::Geq: facts.tightenLower(v, boundary, /*strict=*/false, reasons); break;
            case Relation::Lt:  facts.tightenUpper(v, boundary, /*strict=*/true,  reasons); break;
            case Relation::Leq: facts.tightenUpper(v, boundary, /*strict=*/false, reasons); break;
            case Relation::Eq:
                facts.tightenLower(v, boundary, /*strict=*/false, reasons);
                facts.tightenUpper(v, boundary, /*strict=*/false, reasons);
                break;
            default: break;
        }
    }

    // Build IntervalConstraint list for the multi-var (potentially nonlinear)
    // constraints. Skip the single-var linear ones we already used as bounds
    // (they would trivially refute themselves if inconsistent).
    std::vector<IntervalConstraint> intervalCs;
    intervalCs.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        intervalCs.push_back({c.poly, c.rel, c.reason});
    }
    // First try plain interval refutation (cheap, every call).
    auto conflictOpt = tryRefuteByPolynomialInterval(intervalCs, facts, *kernel_);
    // If no plain conflict, try iterative factoring + back-prop (closes MGC-class).
    // This is the EXPENSIVE part (maxIter back-prop passes over ALL constraints) and
    // re-running it on every Standard cb_propagate during a SAT search is the overhead
    // that times out SAT cases (mgc_09/10: sat→TO; iter 24/25). THROTTLE its cadence:
    // run on the first call (catch quick UNSAT) then only every K-th call. SOUND — a
    // conflict is still found, at most K-1 checks later; SAT cases pay K× less factoring.
    // Tunable XOLVER_NRA_OSF_FACTOR_CADENCE (default 1 = unchanged behaviour).
    static const long factorCadence = []() {
        long v = env::paramInt("XOLVER_NRA_OSF_FACTOR_CADENCE", 1);
        return v > 0 ? v : 1;
    }();
    static thread_local long osfCalls = 0;
    long n = ++osfCalls;
    if (!conflictOpt && (n == 1 || (n % factorCadence) == 0)) {
        conflictOpt = tryRefuteByIterativeFactoring(intervalCs, facts, *kernel_, /*maxIter=*/6);
    }
    if (!conflictOpt) return std::nullopt;

    TheoryConflict tc;
    tc.clause = std::move(conflictOpt->reasons);
    if (xolver::env::diag("XOLVER_NRA_OSF_DIAG")) {
        std::fprintf(stderr, "[XOLVER_NRA_OSF_PRUNE] UNSAT: %s reasons=%zu\n",
                     conflictOpt->explanation.c_str(), tc.clause.size());
    }
    return TheoryCheckResult::mkConflict(std::move(tc));
}

// XOLVER_NRA_PREELIM (default OFF): affine-equality pre-elimination + reduced CDCAC.
//
// CAD (and CDCAC) is doubly-exponential in #variables. The hycomp BMC SAT cases
// couple ~20+ vars, many of which are `_def_*` intermediates defined by LINEAR
// equalities. Eliminating those before CDCAC shrinks the variable count CDCAC
// faces — the lever this stage provides.
//
//   1. Run the presolve fixpoint (integerDomain=false). It records every affine
//      substitution `v = (linear expr over remaining vars)` in substMap, already
//      transitively composed (registerSubstitution reduces values by existing
//      substs and back-substitutes), each tagged with a ledger fact index whose
//      flattenReasons gives the defining-equality SAT literals.
//   2. Substitute every eliminated var out of each ORIGINAL constraint poly.
//   3. Build a reduced CdcacInput (varOrder = remaining vars, lexicographic) and
//      solve with a lazily-built CdcacCore + libpoly backend.
//   4. UNSAT: union EVERY eliminated var's defining-equality reason into the
//      conflict (a superset is sound; omitting one would be a too-strong /
//      false-UNSAT clause — detection-sound ≠ explanation-sound).
//   5. SAT: reconstruct each eliminated var by evaluating its (composed, over
//      remaining vars) defining expr on the solved model, assemble the full real
//      model, and validate over the ORIGINAL presolveConstraints_ via the exact
//      kernel sign (invariant 1 — never return consistent() on the reduced set).
//   6. Unknown / anything unsound to reconstruct ⇒ nullopt (fall to stageCdcac).
//
// Flag OFF ⇒ returns nullopt at the gate (default path byte-identical). No-op
// without XOLVER_HAS_LIBPOLY (CDCAC needs the libpoly algebra backend).
std::optional<TheoryCheckResult> NraSolver::stageNraPreElim(TheoryLemmaStorage& /*lemmaDb*/,
                                                            TheoryEffort /*effort*/) {
    if (!enablePreElim_) return std::nullopt;
#ifndef XOLVER_HAS_LIBPOLY
    return std::nullopt;
#else
    // Collect the live polynomial constraints (skip non-polynomial placeholders).
    std::vector<PresolveCstr> liveCstrs;
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;
        liveCstrs.push_back(c);
    }
    if (liveCstrs.empty()) return std::nullopt;

    // --- Step 1: presolve fixpoint → affine substitutions. -------------------
    // Same iter#22 deadline as stagePresolve above (this is the preelim path
    // that also calls presolve as Step 1 before CDCAC; identical cost profile,
    // identical 50 ms default cap, identical soundness story).
    static const long preelimPresolveBudgetMs =
        env::paramLong("XOLVER_NRA_PRESOLVE_BUDGET_MS", 50);
    PresolveEngine presolve(kernel_.get(), /*integerDomain=*/false);
    std::vector<std::optional<RationalPolynomial>> rps;  // cached RationalPolynomial per cstr
    rps.reserve(liveCstrs.size());
    for (const auto& c : liveCstrs) {
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) return std::nullopt;  // cannot reason; defer to plain CDCAC
        presolve.addAtom(*rp, c.rel, c.reason);
        rps.push_back(rp);
    }
    auto preelimDeadline =
        (preelimPresolveBudgetMs > 0)
            ? std::chrono::steady_clock::now() +
                  std::chrono::milliseconds(preelimPresolveBudgetMs)
            : std::chrono::steady_clock::time_point::max();
    auto pr = presolve.run(preelimDeadline);
    // A presolve Conflict here is handled by stagePresolve already; if it fires
    // we still emit it (sound). A Lemma is a SAT-core split — defer to the normal
    // pipeline by NOT consuming it here (stagePresolve ran first anyway).
    if (pr.kind == PresolveResult::Kind::Conflict)
        return TheoryCheckResult::mkConflict(pr.conflict);

    const PresolveState& ps = presolve.state();
    // Each entry: eliminated var → (defining expr over remaining vars, reason lits).
    struct Elim { VarId var; RationalPolynomial expr; std::vector<SatLit> reasons; };
    std::vector<Elim> elims;
    for (const auto& [v, entry] : ps.substMap) {
        std::vector<SatLit> reasons = ps.ledger.flattenReasons(entry.factIndex);
        elims.push_back({v, entry.value, std::move(reasons)});
    }
    if (elims.empty()) return std::nullopt;  // nothing to eliminate → plain CDCAC wins

    // --- Step 2: substitute eliminated vars out of each ORIGINAL constraint. --
    // substMap values are already transitively composed over the non-eliminated
    // variables, so a single pass of substitute() per eliminated var suffices.
    CdcacInput input;
    std::unordered_set<std::string> seen;
    std::vector<std::string> varNames;
    for (size_t i = 0; i < liveCstrs.size(); ++i) {
        RationalPolynomial p = *rps[i];
        for (const auto& e : elims) {
            if (p.contains(e.var)) p = p.substitute(e.var, e.expr);
        }
        p.normalize();
        PolyId pid = p.toPolyId(*kernel_);
        if (pid == NullPoly) return std::nullopt;  // conversion failed → defer
        CdcacConstraint cc;
        cc.poly = pid;
        cc.rel = liveCstrs[i].rel;
        cc.reason = liveCstrs[i].reason;
        input.constraints.push_back(std::move(cc));
        for (const auto& vn : kernel_->variables(pid)) {
            if (seen.insert(vn).second) varNames.push_back(vn);
        }
    }
    std::sort(varNames.begin(), varNames.end());
    for (const auto& vn : varNames) input.varOrder.push_back(kernel_->getOrCreateVar(vn));

    {
        std::ofstream pe("/tmp/nrapreelim.txt", std::ios::app);
        pe << "[NRAPREELIM] constraints=" << liveCstrs.size()
           << " eliminated=" << elims.size()
           << " remainingVars=" << input.varOrder.size() << "\n";
        pe.flush();
    }

    // --- Step 3: solve a reduced CDCAC over the remaining variables. ---------
    if (!preElimCore_) {
        preElimAlgebra_ = std::make_unique<LibpolyBackend>(kernel_.get());
        preElimCore_ = std::make_unique<CdcacCore>(kernel_.get(), preElimAlgebra_.get());
    }
    CdcacResult result = preElimCore_->solve(input);

    switch (result.status) {
        case CdcacStatus::Unsat: {
            // Real-relaxation covering-UNSAT over the reduced (substituted) system
            // ⇒ UNSAT of the original (the eliminated vars are functionally pinned
            // by their defining equalities). CdcacCore already downgrades an
            // uncertified covering to Unknown, so a Unsat reaching here is a
            // trustworthy empty-covering proof. Thread in EVERY eliminated var's
            // defining-equality reason (a superset is sound; OMITTING one would be
            // a too-strong / false-UNSAT clause).
            std::vector<SatLit> reasons;
            if (result.unsat) reasons = ReasonManager::minimize(result.unsat->covering);
            for (const auto& e : elims)
                reasons.insert(reasons.end(), e.reasons.begin(), e.reasons.end());
            std::ofstream pe("/tmp/nrapreelim.txt", std::ios::app);
            pe << "[NRAPREELIM] verdict=UNSAT reasons=" << reasons.size() << "\n";
            pe.flush();
            return TheoryCheckResult::mkConflict(ReasonManager::toConflict(reasons));
        }
        case CdcacStatus::Sat: {
            if (!result.model) return std::nullopt;
            const SamplePoint& s = *result.model;
            // Solved model over the remaining vars. Reconstruct eliminated vars by
            // evaluating their (composed, over-remaining-vars) defining expr.
            // Accept ONLY a fully-rational sample (algebraic coordinates can't be
            // reconstructed exactly through substitute/sgn here → defer to CDCAC).
            std::unordered_map<std::string, mpq_class> model;
            for (size_t i = 0; i < s.varOrder.size() && i < s.values.size(); ++i) {
                const RealAlg& v = s.values[i];
                if (!v.isRational()) return std::nullopt;
                model[std::string(kernel_->varName(s.varOrder[i]))] = v.rational;
            }
            // Reconstruct eliminated vars. Their defining exprs are over the
            // remaining (solved) vars only, so a single eval per var is exact.
            for (const auto& e : elims) {
                RationalPolynomial expr = e.expr;
                // Substitute each solved value into expr; result must be constant.
                for (const auto& [name, val] : model) {
                    auto vid = kernel_->findVar(name);
                    if (vid && expr.contains(*vid))
                        expr = expr.substituteRational(*vid, val);
                }
                // Any eliminated var the expr still references (chained def) — fold
                // those too, in case substMap composition left a residual.
                for (const auto& e2 : elims) {
                    if (e2.var == e.var) continue;
                    // Not expected (composed away), but guard: cannot resolve → defer.
                    if (expr.contains(e2.var)) return std::nullopt;
                }
                if (!expr.isConstant()) return std::nullopt;  // can't pin → defer
                model[std::string(kernel_->varName(e.var))] = expr.constantValue();
            }
            // --- Step 5: validate over the ORIGINAL constraints (invariant 1). --
            bool allHold = true;
            for (const auto& c : liveCstrs) {
                std::unordered_map<std::string, mpq_class> evalModel = model;
                for (const auto& vn : kernel_->variables(c.poly))
                    evalModel.emplace(vn, mpq_class(0));  // 0-fill any absent (none expected)
                int sg = kernel_->sgn(c.poly, evalModel);
                bool ok = false;
                switch (c.rel) {
                    case Relation::Eq:  ok = (sg == 0); break;
                    case Relation::Geq: ok = (sg >= 0); break;
                    case Relation::Leq: ok = (sg <= 0); break;
                    case Relation::Gt:  ok = (sg > 0);  break;
                    case Relation::Lt:  ok = (sg < 0);  break;
                    case Relation::Neq: ok = (sg != 0); break;
                }
                if (!ok) { allHold = false; break; }
            }
            std::ofstream pe("/tmp/nrapreelim.txt", std::ios::app);
            pe << "[NRAPREELIM] verdict=SAT validated=" << (allHold ? "yes" : "no") << "\n";
            pe.flush();
            if (allHold) return TheoryCheckResult::consistent();
            return std::nullopt;  // validation failed → fall to plain CDCAC
        }
        case CdcacStatus::Unknown: {
            std::ofstream pe("/tmp/nrapreelim.txt", std::ios::app);
            pe << "[NRAPREELIM] verdict=UNKNOWN reason="
               << static_cast<int>(result.unknownReason) << "\n";
            pe.flush();
            return std::nullopt;
        }
    }
    return std::nullopt;
#endif
}

// XOLVER_NRA_SUBTROPICAL SAT-fast-path (default OFF). A cheap, incomplete
// witness search "at infinity" run before the full CAD. It produces a CANDIDATE
// assignment; every active original constraint is then exact-validated via the
// kernel sign (invariant 1). SAT only on a validated model (stored in
// satFastModel_ so getModel() reports it); otherwise nullopt → fall to CDCAC.
std::optional<TheoryCheckResult> NraSolver::stageSubtropical(TheoryLemmaStorage& /*lemmaDb*/,
                                                             TheoryEffort effort) {
    if (!enableSubtropical_) return std::nullopt;
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
    SubtropicalResult r = finder.find(subCons, vars);
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
            if (xolver::env::diag("XOLVER_NRA_SUBTROP_DIAG")) {
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

// XOLVER_NRA_INT_PROBE — structural-integer probe (mgc-class SAT-fast-path).
// Sibling of stageSubtropical. Enumerates small integer + dyadic candidates
// for the highest-exponent variables (which z3-nlsat's decision heuristic
// gravitates toward on mgc-style problems), validates each candidate via
// the kernel sign (invariant 1). Pure NRA only; combination/N-O mode falls
// through because interface (dis)equalities live outside presolveConstraints_.
std::optional<TheoryCheckResult> NraSolver::stageIntegerProbe(
        TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort effort) {
    if (xolver::env::diag("XOLVER_NRA_INT_PROBE_DIAG")) {
        std::ofstream dst("/tmp/int_probe.txt", std::ios::app);
        dst << "[INT-PROBE] called effort=" << (int)effort
            << " presolve=" << presolveConstraints_.size() << "\n";
        dst.flush();
    }
    static const bool enabled = [] {
        return xolver::env::flag("XOLVER_NRA_INT_PROBE");
    }();
    if (!enabled) return std::nullopt;
    // Run at FIRST effort entry (typically Standard) — CDCAC may not survive
    // to Full effort on mgc-class. Sound: a kernel-validated rational point
    // is SAT at any effort (invariant 1). One-shot per solve.
    (void)effort;
    if (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty())
        return std::nullopt;
    if (presolveConstraints_.empty()) return std::nullopt;

    // No one-shot lock: each round the probe re-attempts; the value-split
    // hint dedup is per-var in intProbeValueSplitDone_ (cleared on reset).

    bool diagOn = (xolver::env::diag("XOLVER_NRA_INT_PROBE_DIAG"));
    std::ofstream st;
    if (diagOn) {
        st.open("/tmp/int_probe.txt", std::ios::app);
        st << "[INT-PROBE] enter; constraints=" << presolveConstraints_.size() << "\n";
        st.flush();
    }

    std::vector<StructuralIntegerProbe::Constraint> cons;
    cons.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) {
            if (diagOn) { st << "[INT-PROBE] NullPoly bail\n"; st.flush(); }
            return std::nullopt;
        }
        cons.push_back({c.poly, c.rel});
    }

    auto modelOpt = StructuralIntegerProbe::tryProbe(cons, *kernel_);
    if (!modelOpt) {
        if (diagOn) { st << "[INT-PROBE] no model found; trying value-split hint\n"; st.flush(); }
        // Hint path: even when full enum doesn't validate a model, the
        // structural variable (highest exponent) and small-integer candidate
        // are likely SAT decisions. Emit a tautological 3-way value-split
        // lemma `(< v c) | (= v c) | (> v c)` so SAT branches on the
        // hypothesis the way nlsat's decision heuristic does. This is the
        // same pattern as stageNraSignSplit — biasing the SAT decision tree
        // without committing to the guess.
        if (registry_) {
            // Pick highest-exponent variable that hasn't been hinted yet.
            std::unordered_map<VarId, int> maxExp;
            for (const auto& c : presolveConstraints_) {
                if (c.poly == NullPoly) continue;
                auto termsOpt = kernel_->terms(c.poly);
                if (!termsOpt) continue;
                for (const auto& term : *termsOpt) {
                    for (const auto& [vid, exp] : term.powers) {
                        if (exp > maxExp[vid]) maxExp[vid] = exp;
                    }
                }
            }
            VarId pick = NullVar;
            int bestExp = 1;
            for (const auto& [v, e] : maxExp) {
                if (e <= bestExp) continue;
                if (intProbeValueSplitDone_.count(v)) continue;
                pick = v; bestExp = e;
            }
            if (pick != NullVar) {
                // Try candidate value c = 2 first (matches z3 nlsat's
                // preference on this benchmark family for high-exp vars).
                static const mpq_class kHintValue(2);
                PolyId vPoly = kernel_->mkVar(pick);
                SatLit ltL = registry_->getOrCreatePolynomialAtom(
                    vPoly, Relation::Lt, kHintValue, TheoryId::LRA);
                SatLit eqL = registry_->getOrCreatePolynomialAtom(
                    vPoly, Relation::Eq, kHintValue, TheoryId::LRA);
                SatLit gtL = registry_->getOrCreatePolynomialAtom(
                    vPoly, Relation::Gt, kHintValue, TheoryId::LRA);
                if (ltL.var != 0 && eqL.var != 0 && gtL.var != 0) {
                    TheoryLemma hint{{eqL, ltL, gtL}};
                    intProbeValueSplitDone_.insert(pick);
                    if (diagOn) {
                        st << "[INT-PROBE] HINT emitted: ("
                           << kernel_->varName(pick)
                           << " = " << kHintValue.get_str()
                           << ") | (< " << kHintValue.get_str()
                           << ") | (> " << kHintValue.get_str() << ")\n";
                        st.flush();
                    }
                    return TheoryCheckResult::mkLemma(std::move(hint));
                }
            }
        }
        return std::nullopt;
    }

    if (diagOn) {
        st << "[INT-PROBE] SAT model size=" << modelOpt->size() << "\n";
        for (const auto& [v, q] : *modelOpt) {
            st << "  " << kernel_->varName(v) << " = " << q.get_str(10) << "\n";
        }
        st.flush();
    }
    satFastModel_ = std::move(*modelOpt);
    return TheoryCheckResult::consistent();
}

// XOLVER_NRA_EQ_CASCADE — equality-cascade SAT solver (mgc-class). Assign the
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
    static const bool enabled = [] {
        // Promoted default-ON (#NRA-LS-E iter 2): pure-rational + exact-validated
        // over ALL active constraints (invariant 1) ⇒ sound by construction, and
        // it never invokes libpoly root isolation, so it dodges the nlsat-path
        // heap-corruption class entirely. Recovers mgc_09/mgc_10 (CDCAC times out
        // projecting their degree-16/18 atoms). Disable with XOLVER_NRA_EQ_CASCADE=0.
        const char* e = std::getenv("XOLVER_NRA_EQ_CASCADE");
        return !(e && *e == '0');
    }();
    if (!enabled) return std::nullopt;
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

// Algebraic square-cascade (default ON; XOLVER_NRA_SQUARE_CASCADE=0 disables). Builds
// and EXACT-validates a Q(sqrt c) model for square-defined systems the rational
// eq-cascade can't (v^2 = non-square => algebraic root). Sound by construction:
// trySquareCascade returns true only after checking every original constraint's exact
// sign at the constructed model (invariant 1); on any inconclusive/failing check it
// returns false and we fall through to CAC/Collins unchanged.
std::optional<TheoryCheckResult> NraSolver::stageSquareCascade(
        TheoryLemmaStorage& /*lemmaDb*/, TheoryEffort /*effort*/) {
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NRA_SQUARE_CASCADE");
        return !(e && *e == '0');
    }();
    if (!enabled) return std::nullopt;
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
