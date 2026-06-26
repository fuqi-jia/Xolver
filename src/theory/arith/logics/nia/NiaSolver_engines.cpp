#include "theory/arith/logics/nia/NiaSolver.h"
#include "theory/arith/logics/nia/NiaSolverDetail.h"  // collectVars / dispatch-signature helpers (shared across split TUs)
#include <algorithm>
#include "theory/arith/logics/dl/DifferenceGraph.h"
#include "theory/arith/logics/dl/BellmanFord.h"
#include "theory/arith/logics/nia/preprocess/VariablePartition.h"
#include "theory/arith/Reasoner.h"
#include <random>
#include "theory/arith/logics/nia/search/NiaLinearizationAdapter.h"
#include "theory/arith/logics/nia/search/NiaIcpAdapter.h"
#include "theory/arith/kernel/icp/IcpTypes.h"
#include "theory/arith/logics/nra/core/CdcacCore.h"
#include "theory/arith/logics/nra/core/CdcacConstraint.h"
#include "theory/arith/logics/nra/engine/ReasonManager.h"
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/logics/nra/backend/LibpolyBackend.h"
#include "theory/arith/logics/nia/farkas/LeafFarkasLia.h"
#include "theory/arith/logics/nra/reasoners/NlaCutsRunner.h"           // Stage 3 Phase C-3
#include "theory/arith/kernel/poly/RationalPolynomial.h"          // Stage 3 Phase C-3
#endif
#include "theory/arith/kernel/linear/LinearExpr.h"
#include "theory/arith/logics/nia/search/NiaLinearDecider.h"  // embedded complete-LIA (nia.linear-decide)
#include "theory/arith/logics/nia/reasoners/OmegaTest.h"        // nia.omega: sound linear-integer UNSAT
#include "theory/arith/logics/nia/reasoners/SmallPrimeModular.h" // nia.small-prime-modular: GF(p) schedule
#include "theory/arith/logics/nia/reasoners/IntBoundProp.h"      // nia.int-bound-prop: integer interval refutation
#include "theory/arith/kernel/linearizer/NonlinearTermAbstraction.h"
#include "theory/arith/kernel/linear/LinearConstraintNormalizer.h"
#include "theory/core/LogicFeatureDetector.h"
#include "theory/arith/kernel/presolve/Presolve.h"
#include "theory/arith/kernel/search/CompleteFiniteDomainEnumerator.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "proof/ArithModelValidator.h"
#include "util/EnvParam.h"
#include <functional>
#include <set>
#include "theory/arith/logics/nia/farkas/FarkasOrDetector.h"
#include "theory/arith/logics/nia/farkas/FarkasOrSolver.h"
#include "theory/arith/logics/nia/farkas/FarkasOrModelAssembler.h"
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

// nia.omega — Pugh's Omega test (sound linear-integer UNSAT). See OmegaTest.{h,cpp}
// (engine: equality elimination + real-shadow FM + integer tightening; fuzz-validated
// 0 false-UNSAT vs z3). This stage builds the linear-INTEGER relaxation of the active
// system and asks the engine; on a proven UNSAT it emits a conflict over the
// contributing constraints' reasons. SOUND: nonlinear monomials → FREE int vars and
// dropped Neq are both relaxations (relaxed-UNSAT ⇒ original-UNSAT); real vars ⇒ skip.
std::optional<TheoryCheckResult> NiaSolver::stageOmega(TheoryLemmaStorage&, TheoryEffort effort) {
    if (!enableOmega_) return std::nullopt;
    if (effort != TheoryEffort::Full) return std::nullopt;  // refute complete models
    if (normalized_.empty() || !kernel_) return std::nullopt;

    // Soundness gate (cached): integer reasoning is unsound if any variable is real.
    if (omegaSafe_ < 0)
        omegaSafe_ = (coreIr_ && !LogicFeatureDetector(*coreIr_).detect().hasRealVar) ? 1 : 0;
    if (omegaSafe_ != 1) return std::nullopt;

    // Soundness firewall: the conflict clause may ONLY contain literals currently
    // true on the SAT trail. So build the relaxation from constraints whose reason
    // is live (skip derived/definitional ones with off-trail reasons — dropping
    // them only relaxes, keeping Omega-UNSAT ⇒ original-UNSAT sound, while every
    // emitted conflict literal stays a real, backtrackable SAT decision).
    std::unordered_map<SatVar, bool> asserted;
    asserted.reserve(state_.trail.size());
    for (const auto& a : state_.trail) asserted[a.lit.var] = a.lit.sign;
    auto live = [&](const SatLit& r) {
        auto it = asserted.find(r.var);
        return it != asserted.end() && it->second == r.sign;
    };

    NonlinearTermAbstraction abstraction(*kernel_);
    std::vector<omega::Constraint> ocs;
    std::vector<SatLit> reasons;
    std::map<std::string, int> varIndex;
    auto idxOf = [&](const std::string& n) {
        return varIndex.emplace(n, static_cast<int>(varIndex.size())).first->second;
    };
    auto asInt = [](const mpq_class& q, mpz_class& out) {
        if (q.get_den() != 1) return false;
        out = q.get_num();
        return true;
    };
    for (const auto& c : normalized_) {
        if (c.rel == Relation::Neq) continue;            // drop Neq (sound: subset-UNSAT ⇒ UNSAT)
        if (!live(c.reason)) continue;                   // off-trail reason ⇒ exclude (relaxation)
        auto abs = abstraction.abstract(c.poly);
        if (abs.unsupported) return std::nullopt;        // cannot relax ⇒ no claim
        auto zlc = LinearConstraintNormalizer::fromPolynomialZero(
            *kernel_, abs.linearizedPoly, c.rel, SortKind::Int);
        if (!zlc) return std::nullopt;                   // not linear after abstraction ⇒ no claim
        omega::Constraint oc;
        bool ok = true;
        for (const auto& t : zlc->expr.terms) {
            mpz_class a;
            if (!asInt(t.coeff, a)) { ok = false; break; }
            if (a != 0) oc.coeffs[idxOf(t.var)] += a;
        }
        mpz_class cst;
        if (!ok || !asInt(zlc->expr.constant, cst)) return std::nullopt;
        oc.constant = cst;
        oc.rel = c.rel == Relation::Eq  ? omega::Constraint::Eq
               : c.rel == Relation::Leq ? omega::Constraint::Leq
                                        : omega::Constraint::Geq;
        ocs.push_back(std::move(oc));
        reasons.push_back(c.reason);
    }
    if (ocs.size() < 2) return std::nullopt;
    const bool diag = xolver::env::diag("XOLVER_NIA_OMEGA_DIAG");
    const bool unsat = omega::decide(ocs) == omega::Result::Unsat;
    if (diag) {
        size_t nv = 0;
        for (const auto& c : ocs) nv = std::max(nv, c.coeffs.empty() ? size_t(0)
                                                    : c.coeffs.rbegin()->first + 1);
        std::fprintf(stderr, "[OMEGA] constraints=%zu vars~%zu -> %s\n",
                     ocs.size(), nv, unsat ? "UNSAT" : "SatOrUnknown");
    }
    if (unsat)
        return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
    return std::nullopt;
}

// nia.small-prime-modular — cheap GF(p) congruence refutation (see SmallPrimeModular).
// Builds the linear-INTEGER relaxation of the active EQUALITY constraints (nonlinear
// monomials → free int vars, a relaxation) and asks whether the system is inconsistent
// modulo some small prime; if so, emits a conflict over those equalities' reasons.
// Runs at Standard effort too, so a derived obstruction like 2x=1 prunes the search
// before a complete model is reached. SOUND: GF(p)-infeasible ⇒ Z-infeasible, and the
// abstraction/firewall are the same relaxations as nia.omega.
std::optional<TheoryCheckResult> NiaSolver::stageSmallPrimeModular(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableSmallPrimeModular_) return std::nullopt;
    if (normalized_.empty() || !kernel_) return std::nullopt;

    if (omegaSafe_ < 0)   // shared pure-integer soundness gate (no real vars)
        omegaSafe_ = (coreIr_ && !LogicFeatureDetector(*coreIr_).detect().hasRealVar) ? 1 : 0;
    if (omegaSafe_ != 1) return std::nullopt;

    std::unordered_map<SatVar, bool> asserted;
    asserted.reserve(state_.trail.size());
    for (const auto& a : state_.trail) asserted[a.lit.var] = a.lit.sign;
    auto live = [&](const SatLit& r) {
        auto it = asserted.find(r.var);
        return it != asserted.end() && it->second == r.sign;
    };

    NonlinearTermAbstraction abstraction(*kernel_);
    std::vector<omega::Constraint> ocs;
    std::vector<SatLit> reasons;
    std::map<std::string, int> varIndex;
    auto idxOf = [&](const std::string& n) {
        return varIndex.emplace(n, static_cast<int>(varIndex.size())).first->second;
    };
    auto asInt = [](const mpq_class& q, mpz_class& out) {
        if (q.get_den() != 1) return false;
        out = q.get_num();
        return true;
    };
    for (const auto& c : normalized_) {
        if (c.rel != Relation::Eq) continue;             // modular reasoning uses equalities only
        if (!live(c.reason)) continue;                   // off-trail reason ⇒ exclude (relaxation)
        auto abs = abstraction.abstract(c.poly);
        if (abs.unsupported) continue;                   // cannot relax this row ⇒ skip it (still sound)
        auto zlc = LinearConstraintNormalizer::fromPolynomialZero(
            *kernel_, abs.linearizedPoly, c.rel, SortKind::Int);
        if (!zlc) continue;
        omega::Constraint oc;
        bool ok = true;
        for (const auto& t : zlc->expr.terms) {
            mpz_class a;
            if (!asInt(t.coeff, a)) { ok = false; break; }
            if (a != 0) oc.coeffs[idxOf(t.var)] += a;
        }
        mpz_class cst;
        if (!ok || !asInt(zlc->expr.constant, cst)) continue;
        oc.constant = cst;
        oc.rel = omega::Constraint::Eq;
        ocs.push_back(std::move(oc));
        reasons.push_back(c.reason);
    }
    if (ocs.empty()) return std::nullopt;
    const bool unsat = modular::decide(ocs) == modular::Result::Unsat;
    if (xolver::env::diag("XOLVER_NIA_SMALL_PRIME_MODULAR_DIAG"))
        std::fprintf(stderr, "[MODULAR] eqs=%zu -> %s\n",
                     ocs.size(), unsat ? "UNSAT" : "SatOrUnknown");
    if (unsat)
        return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
    return std::nullopt;
}

// nia.int-bound-prop — integer interval contraction (see IntBoundProp). Builds the
// integer relaxation, seeds variable domains from the asserted SINGLE-variable bound
// atoms (a·x+c {≥,≤} 0 → an integer ceil/floor bound), and contracts over the
// equalities; an emptied domain is a sound integer-infeasibility ⇒ conflict. This
// refutes bound×equality obstructions (e.g. x=2y ∧ x=1 ⇒ 2y=1) that the equalities-only
// modular reasoner misses. SOUND: the same abstraction/firewall relaxations as nia.omega,
// plus interval contraction preserves every integer solution. (Domain-narrowing
// PROPAGATION — feeding tightened bounds back to prune — is the separate B1+B2.2b.)
std::optional<TheoryCheckResult> NiaSolver::stageIntBoundProp(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableIntBoundProp_) return std::nullopt;
    if (normalized_.empty() || !kernel_) return std::nullopt;

    if (omegaSafe_ < 0)
        omegaSafe_ = (coreIr_ && !LogicFeatureDetector(*coreIr_).detect().hasRealVar) ? 1 : 0;
    if (omegaSafe_ != 1) return std::nullopt;

    std::unordered_map<SatVar, bool> asserted;
    asserted.reserve(state_.trail.size());
    for (const auto& a : state_.trail) asserted[a.lit.var] = a.lit.sign;
    auto live = [&](const SatLit& r) {
        auto it = asserted.find(r.var);
        return it != asserted.end() && it->second == r.sign;
    };

    NonlinearTermAbstraction abstraction(*kernel_);
    std::vector<omega::Constraint> ocs;
    std::vector<SatLit> eqReasons, seedReasons;
    std::map<int, intprop::Bound> seedBounds;
    std::map<std::string, int> varIndex;
    auto idxOf = [&](const std::string& n) {
        return varIndex.emplace(n, static_cast<int>(varIndex.size())).first->second;
    };
    auto asInt = [](const mpq_class& q, mpz_class& out) {
        if (q.get_den() != 1) return false;
        out = q.get_num();
        return true;
    };
    auto ceildiv = [](const mpz_class& a, const mpz_class& m) {  // m > 0
        mpz_class q; mpz_cdiv_q(q.get_mpz_t(), a.get_mpz_t(), m.get_mpz_t()); return q;
    };
    auto floordiv = [](const mpz_class& a, const mpz_class& m) {  // m > 0
        mpz_class q; mpz_fdiv_q(q.get_mpz_t(), a.get_mpz_t(), m.get_mpz_t()); return q;
    };
    auto tightenLo = [&](int v, const mpz_class& lo, const SatLit& r) {
        intprop::Bound& b = seedBounds[v];
        if (!b.hasLo || lo > b.lo) { b.lo = lo; b.hasLo = true; }
        seedReasons.push_back(r);
    };
    auto tightenHi = [&](int v, const mpz_class& hi, const SatLit& r) {
        intprop::Bound& b = seedBounds[v];
        if (!b.hasHi || hi < b.hi) { b.hi = hi; b.hasHi = true; }
        seedReasons.push_back(r);
    };

    for (const auto& c : normalized_) {
        if (c.rel == Relation::Neq) continue;            // drop Neq (sound)
        if (!live(c.reason)) continue;                   // off-trail reason ⇒ exclude (relaxation)
        auto abs = abstraction.abstract(c.poly);
        if (abs.unsupported) continue;
        auto zlc = LinearConstraintNormalizer::fromPolynomialZero(
            *kernel_, abs.linearizedPoly, c.rel, SortKind::Int);
        if (!zlc) continue;
        omega::Constraint oc;
        bool ok = true;
        for (const auto& t : zlc->expr.terms) {
            mpz_class a;
            if (!asInt(t.coeff, a)) { ok = false; break; }
            if (a != 0) oc.coeffs[idxOf(t.var)] += a;
        }
        mpz_class cst;
        if (!ok || !asInt(zlc->expr.constant, cst)) continue;
        oc.constant = cst;
        oc.rel = c.rel == Relation::Eq  ? omega::Constraint::Eq
               : c.rel == Relation::Leq ? omega::Constraint::Leq
                                        : omega::Constraint::Geq;

        if (oc.rel == omega::Constraint::Eq) {
            eqReasons.push_back(c.reason);
            ocs.push_back(std::move(oc));
        } else if (oc.coeffs.size() == 1) {
            // Single-variable inequality ⇒ an integer ceil/floor bound (the seed).
            const int v = oc.coeffs.begin()->first;
            const mpz_class a = oc.coeffs.begin()->second;   // ≠ 0
            const mpz_class m = (a < 0) ? mpz_class(-a) : a; // |a|
            const mpz_class K = -oc.constant;                // a·x {≥,≤} K
            const bool geq = (oc.rel == omega::Constraint::Geq);
            if ((geq && a > 0) || (!geq && a < 0))      tightenLo(v, ceildiv(geq ? K : -K, m), c.reason);
            else                                         tightenHi(v, floordiv(geq ? -K : K, m), c.reason);
        }
        // multi-variable inequalities are ignored (this cut handles equalities + bounds).
    }
    if (ocs.empty()) return std::nullopt;

    const bool unsat = intprop::propagate(ocs, seedBounds) == intprop::Result::Unsat;
    if (xolver::env::diag("XOLVER_NIA_INT_BOUND_PROP_DIAG"))
        std::fprintf(stderr, "[INTBOUND] eqs=%zu seeds=%zu -> %s\n",
                     ocs.size(), seedReasons.size(), unsat ? "UNSAT" : "Ok");
    if (unsat) {
        std::vector<SatLit> reasons = std::move(eqReasons);
        reasons.insert(reasons.end(), seedReasons.begin(), seedReasons.end());
        return TheoryCheckResult::mkConflict(TheoryConflict{std::move(reasons)});
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageDio(TheoryLemmaStorage&, TheoryEffort) {
    static const bool enabled = [] {
        return xolver::env::flag("XOLVER_NIA_DIO");
    }();
    if (!enabled) return std::nullopt;

    // (A) Lattice-step + bound tightening (arith-dio-tighten). Marshals the live
    // equalities / disequalities / inequalities (normalized_) and the per-variable
    // bounds (domains_, populated by the earlier linear-domain stage) into the
    // shared DioReasoner::tightenConflict — which folds complementary inequality
    // pairs + pinned bounds into the lattice. Refutes the QF_(A)NIA
    // integer-Diophantine cluster (in-de42 etc.) when NIA gets the check.
    {
        std::vector<DioLinForm> cons;
        for (const auto& c : normalized_) {
            if (c.rel != Relation::Eq && c.rel != Relation::Neq &&
                c.rel != Relation::Leq && c.rel != Relation::Geq) continue;
            auto termsOpt = kernel_->terms(c.poly);
            if (!termsOpt) continue;
            DioLinForm f;
            f.cst = 0;
            f.rel = c.rel;
            f.reason = c.reason;
            bool linear = true;
            for (const auto& t : *termsOpt) {
                if (t.powers.empty()) { f.cst += t.coefficient; continue; }
                if (t.powers.size() != 1 || t.powers[0].second != 1) { linear = false; break; }
                f.coeffs.emplace_back(std::string(kernel_->varName(t.powers[0].first)), t.coefficient);
            }
            if (!linear || f.coeffs.empty()) continue;
            cons.push_back(std::move(f));
        }
        std::map<std::string, DioVarBound> bnds;
        for (const auto& [name, dom] : domains_.getAllDomains()) {
            DioVarBound bb;
            if (dom.hasLower) { bb.hasLo = true; bb.lo = dom.lower.value; bb.loReasons = dom.lower.reasons; }
            if (dom.hasUpper) { bb.hasHi = true; bb.hi = dom.upper.value; bb.hiReasons = dom.upper.reasons; }
            bnds.emplace(name, std::move(bb));
        }
        auto conflictOpt = DioReasoner::tightenConflict(cons, bnds);
        if (conflictOpt) return TheoryCheckResult::mkConflict(TheoryConflict{*conflictOpt});
    }

    // (B) Symbolic modular-congruence path (variable-divisor `(mod x y)=c` facts).
    if (modEqConstFacts_.empty() || !registry_ || !coreIr_) return std::nullopt;

    // Build DioCongruences from currently-asserted (mod x m) = c facts:
    //   (mod x m) = c   =>   x ≡ c (mod m)   for a CONSTANT divisor m > 1.
    // (Variable-divisor facts have no constant modulus and are skipped.)
    std::vector<DioCongruence> congs;
    for (const auto& src : modEqConstFacts_) {
        auto satVarOpt = registry_->findSatVarByExprId(src.atomExpr);
        if (!satVarOpt) continue;
        SatLit posLit{*satVarOpt, /*sign=*/false};
        if (!activeSet_.contains(posLit)) continue;

        const auto& xe = coreIr_->get(src.xExpr);
        if (xe.kind != Kind::Variable) continue;
        const auto* nm = std::get_if<std::string>(&xe.payload.value);
        if (!nm) continue;

        const auto& ye = coreIr_->get(src.yExpr);
        if (ye.kind != Kind::ConstInt) continue;  // need a constant modulus
        mpz_class m;
        if (const auto* i = std::get_if<int64_t>(&ye.payload.value)) m = *i;
        else if (const auto* s = std::get_if<std::string>(&ye.payload.value)) m = mpz_class(*s);
        else continue;
        if (m <= 1) continue;

        congs.push_back({kernel_->getOrCreateVar(*nm), src.c, m, posLit});
    }
    if (congs.empty()) return std::nullopt;

    auto r = dio_.run(normalized_, congs);
    if (r.kind == NiaReasoningKind::Conflict)
        return TheoryCheckResult::mkConflict(*r.conflict);
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageGroebner(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableGroebner_) return std::nullopt;
    auto r = groebner_.run(normalized_);
    if (r.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageIcp(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableIcp_) return std::nullopt;
    std::vector<IcpConstraint> cs;
    cs.reserve(normalized_.size());
    for (const auto& c : normalized_) {
        cs.push_back(IcpConstraint{std::nullopt, c.poly, c.rel, c.reason, TheoryId::NIA});
    }
    NiaIcpAdapter adapter(*kernel_, domains_);
    IcpConfig cfg;  // V1 defaults: contract to fixpoint, suggest (not apply) splits
    auto r = adapter.run(cs, cfg);
    if (r.status == IcpStatus::Conflict && r.conflict) {
        return TheoryCheckResult::mkConflict(*r.conflict);
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> NiaSolver::stageCdcac(TheoryLemmaStorage&, TheoryEffort) {
    if (!enableCdcac_ || normalized_.empty()) return std::nullopt;
#ifndef XOLVER_HAS_LIBPOLY
    return std::nullopt;  // CDCAC requires the libpoly algebra backend
#else
    if (!cdcacCore_) {
        cdcacAlgebra_ = std::make_unique<LibpolyBackend>(kernel_.get());
        cdcacCore_ = std::make_unique<CdcacCore>(kernel_.get(), cdcacAlgebra_.get());
    }

    // Pre-elimination (the lever — CAD is doubly-exponential in #vars): substitute
    // every domain-FIXED variable (lb == ub, derived by the earlier cheap stages)
    // into the constraint polynomials and drop it from the CDCAC variable set, so
    // CDCAC faces fewer variables. SOUND only if the substituted vars' bound-reasons
    // are threaded into any UNSAT conflict (detection-sound ≠ explanation-sound).
    std::unordered_map<std::string, mpz_class> fixedVal;
    std::unordered_map<std::string, std::vector<SatLit>> fixedReasons;
    for (const auto& [name, dom] : domains_.getAllDomains()) {
        if (dom.hasLower && dom.hasUpper && dom.lower.value == dom.upper.value) {
            fixedVal[name] = dom.lower.value;
            std::vector<SatLit>& rs = fixedReasons[name];
            rs.insert(rs.end(), dom.lower.reasons.begin(), dom.lower.reasons.end());
            rs.insert(rs.end(), dom.upper.reasons.begin(), dom.upper.reasons.end());
        }
    }

    // Build CdcacInput from the (substituted) constraints; lexicographic base
    // variable order (deterministic). varOrder excludes fixed vars because they
    // no longer appear in the substituted polynomials.
    CdcacInput input;
    std::unordered_set<std::string> seen;
    std::vector<std::string> varNames;
    std::unordered_set<std::string> usedFixed;  // fixed vars actually substituted
    for (const auto& c : normalized_) {
        PolyId p = c.poly;
        if (!fixedVal.empty()) {
            for (const auto& v : kernel_->variables(p)) {
                auto it = fixedVal.find(v);
                if (it == fixedVal.end()) continue;
                if (auto vid = kernel_->findVar(v)) {
                    if (auto sp = kernel_->substituteRational(p, *vid, mpq_class(it->second))) {
                        p = *sp;
                        usedFixed.insert(v);
                    }
                }
            }
        }
        CdcacConstraint cc;
        cc.poly = p;
        cc.rel = c.rel;
        cc.reason = c.reason;
        input.constraints.push_back(std::move(cc));
        for (const auto& v : kernel_->variables(p)) {
            if (seen.insert(v).second) varNames.push_back(v);
        }
    }
    std::sort(varNames.begin(), varNames.end());
    for (const auto& name : varNames) input.varOrder.push_back(kernel_->getOrCreateVar(name));

    CdcacResult result = cdcacCore_->solve(input);
    switch (result.status) {
        case CdcacStatus::Unsat: {
            // Real-relaxation covering-UNSAT ⇒ integer-UNSAT (ℤⁿ⊆ℝⁿ). CdcacCore
            // already downgrades an uncertified covering to Unknown, so a Unsat
            // reaching here is a trustworthy real empty-covering proof. Thread in
            // the bound-reasons of every fixed var we substituted (a superset is
            // sound; OMITTING one would be a too-strong/false-UNSAT clause).
            std::vector<SatLit> reasons;
            if (result.unsat) reasons = ReasonManager::minimize(result.unsat->covering);
            for (const auto& name : usedFixed) {
                const auto& rs = fixedReasons[name];
                reasons.insert(reasons.end(), rs.begin(), rs.end());
            }
            return TheoryCheckResult::mkConflict(ReasonManager::toConflict(reasons));
        }
        case CdcacStatus::Sat: {
            // CDCAC's sample is over the reals (and over the REDUCED variable set).
            // Accept as an integer model ONLY if every solved coordinate is an exact
            // integer; reattach the fixed vars; then validate over the ORIGINAL
            // normalized_ (invariant 1: never return a raw candidate).
            if (!result.model) return std::nullopt;
            const SamplePoint& s = *result.model;
            IntegerModel im;
            for (size_t i = 0; i < s.varOrder.size() && i < s.values.size(); ++i) {
                const RealAlg& v = s.values[i];
                if (!v.isRational() || v.rational.get_den() != 1) return std::nullopt;
                im[std::string(kernel_->varName(s.varOrder[i]))] = v.rational.get_num();
            }
            for (const auto& [name, val] : fixedVal) im[name] = val;
            if (validator_.validate(im, normalized_) == IntegerModelValidator::Result::Valid) {
                currentModel_ = std::move(im);
                return TheoryCheckResult::consistent();
            }
            return std::nullopt;
        }
        case CdcacStatus::Unknown:
            return std::nullopt;
    }
    return std::nullopt;
#endif
}

std::optional<TheoryCheckResult> NiaSolver::stageLinearization(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    // 9.4: Mirror effective active linear bounds to LIA
    if (pendingLinLemmas_.empty() && registry_ && linAdapter_) {
        std::vector<LinearizerActiveAssignment> laas;
        laas.reserve(trail().size());
        for (const auto& a : trail()) {
            laas.push_back({a.level, a.lit, a.atom, a.value});
        }
        auto mirrorLemmas = linAdapter_->mirrorActiveLinearBounds(laas, TheoryId::LIA);
        for (auto& ml : mirrorLemmas) {
            if (!lemmaDb.contains(ml)) {
                lemmaDb.insertIfNew(ml);
                pendingLinLemmas_.push_back(std::move(ml));
            }
        }
    }

    // 9.5: Incremental linearization for nonlinear constraints
    // V1 limited: abstraction lemma + square nonnegativity only.
    // No McCormick, secant, tangent until LIA aux-var handling is verified.
    //
    // H1 (master 2026-06-01 audit): XOLVER_NIA_SECANT (default-OFF)
    // re-enables the upper-bounding square secant cut for NIA. The cut
    // (x^2 <= ((hi+lo)*x - hi*lo)) over a bounded box is a sound valid
    // linear inequality (cvc5 NLext canonical lemma). It was originally
    // gated off pending LIA aux-var handling; the LIA simplex is now
    // stable (lia P4 incremental-beta shipped), so re-enabling is a
    // candidate ship. NRA's NraLinearizationAdapter already runs with
    // emitSquareSecant=true, so the cut-generator code path is
    // production-validated; only the wire-in is opt-in here.
    if (pendingLinLemmas_.empty() && registry_ && linAdapter_) {
        LinearizationConfig cfg;
        cfg.emitAllMcCormick = true;
        static const bool secantOn = [] {
            return xolver::env::flag("XOLVER_NIA_SECANT");
        }();
        cfg.emitSquareSecant = secantOn;
        cfg.emitSquareTangent = true;
        cfg.emitSquareNonneg = true;
        cfg.maxLemmas = 10;
        cfg.maxCutsPerTerm = 4;

        auto lr = linAdapter_->runLinearizer(normalized_, domains_, lemmaDb, cfg);
        if (lr.status == LinearizationStatus::Lemma) {
            for (auto& item : lr.lemmas) {
                if (!lemmaDb.contains(item.lemma)) {
                    lemmaDb.insertIfNew(item.lemma);
                    pendingLinLemmas_.push_back(std::move(item.lemma));
                    if (item.cacheKey) {
                        linAdapter_->markEmitted(*item.cacheKey);
                    }
                }
            }
        }
    }
    return std::nullopt;
}

} // namespace xolver
