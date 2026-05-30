#include "theory/arith/nra/NraSolver.h"
#include "theory/arith/Reasoner.h"
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/presolve/Presolve.h"
#include "theory/arith/poly/RationalPolynomial.h"
#include "util/RealValue.h"                                // XOLVER_NRA_SUBTROPICAL witness model
#include "theory/arith/nra/NraLinearizationAdapter.h"     // XOLVER_NRA_LINEARIZE cut-feeder
#include "theory/arith/nia/preprocess/NiaNormalizer.h"    // XOLVER_NRA_LINEARIZE: normalize nonlinear cstrs
#include "theory/arith/nra/reasoners/SubtropicalSatFinder.h"  // XOLVER_NRA_SUBTROPICAL SAT-fast-path
#include "theory/arith/nra/cac/CacEngine.h"                    // XOLVER_NRA_CAC conflict-driven coverings
#include "theory/arith/refute/SignDefinitenessRefuter.h"       // XOLVER_NRA_SIGN_REFUTE
#include "theory/arith/nra/core/CdcacCore.h"               // XOLVER_NRA_PREELIM reduced CDCAC
#include "theory/arith/nra/core/CdcacConstraint.h"         // XOLVER_NRA_PREELIM
#include "theory/arith/nra/engine/ReasonManager.h"         // XOLVER_NRA_PREELIM conflict reasons
#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/nra/backend/LibpolyBackend.h"       // XOLVER_NRA_PREELIM algebra backend
#endif
#include <cstdlib>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <fstream>

namespace xolver {

NraSolver::NraSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)),
      converter_(std::make_unique<PolynomialConverter>(*kernel_)),
      engine_(kernel_.get()) {
    // Phase 2 reasoner pipeline: presolve fixpoint, then CDCAC.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.presolve",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stagePresolve(db, e); }));
    // XOLVER_NRA_SIGN_REFUTE (default OFF): cheap positive-orthant sign-
    // definiteness UNSAT refuter, right after presolve. nullopt at the gate when OFF.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.sign-refute",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageSignRefute(db, e); }));
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.linearize-probe",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageLinearizeProbe(db, e); }));
    // XOLVER_NRA_PREELIM (default OFF): affine pre-elimination then reduced CDCAC.
    // Runs BEFORE the full-variable CDCAC backstop; nullopt at the gate when OFF.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.preelim",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageNraPreElim(db, e); }));
    // XOLVER_NRA_SUBTROPICAL (default OFF): cheap SAT-fast-path before the full
    // CAD. nullopt at the gate when OFF; runs only at Full effort.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.subtropical",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageSubtropical(db, e); }));
    // XOLVER_NRA_CAC (A/B for the Collins-vs-CAC differential): conflict-driven
    // single-cell CAC as the primary engine, BEFORE the Collins buildClosure.
    // nullopt at the gate when OFF or on CAC-Unknown ⇒ Collins fallback.
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.cac",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCac(db, e); }));
    reasoners_.push_back(std::make_unique<CallbackReasoner>(
        "nra.cdcac",
        [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageCdcac(db, e); }));

    // XOLVER_NRA_PREELIM: read the gate once at construction (mirrors A7's
    // enableCdcac_). OFF ⇒ stageNraPreElim returns nullopt immediately so the
    // default path is byte-identical.
    if (const char* e = std::getenv("XOLVER_NRA_PREELIM"); e && *e && *e != '0')
        enablePreElim_ = true;
    if (const char* e = std::getenv("XOLVER_NRA_SUBTROPICAL"); e && *e && *e != '0')
        enableSubtropical_ = true;
    if (const char* e = std::getenv("XOLVER_NRA_CAC"); e && *e && *e != '0')
        enableCac_ = true;
    if (const char* e = std::getenv("XOLVER_NRA_SIGN_REFUTE"); e && *e && *e != '0')
        enableSignRefute_ = true;
}

// Out-of-line: NraLinearizationAdapter is an incomplete type in the header.
NraSolver::~NraSolver() = default;

void NraSolver::setRegistry(TheoryAtomRegistry* reg) {
    registry_ = reg;
    if (reg) {
        linAdapter_ = std::make_unique<NraLinearizationAdapter>(*kernel_, reg);
    }
}

void NraSolver::onPush() {
    scopeStack_.push_back(activeLits_.size());
    engine_.push();
}

void NraSolver::onPop(uint32_t n) {
    for (uint32_t i = 0; i < n && !scopeStack_.empty(); ++i) {
        size_t targetSize = scopeStack_.back();
        scopeStack_.pop_back();
        activeLits_.resize(targetSize);
    }
    trail_.clear();  // V5: rebuild trail from activeLits on next backtrack
    activeSet_.rebuildFromActive(activeLits_, [](const auto& lit) { return lit; });
    presolveConstraints_.resize(activeLits_.size());
    activeRecords_.resize(activeLits_.size());
    satFastModel_.reset();  // XOLVER_NRA_SUBTROPICAL: assignment changed → witness stale
    engine_.pop(n);
}

void NraSolver::onReset() {
    engine_.reset();
    activeLits_.clear();
    trail_.clear();
    presolveConstraints_.clear();
    activeRecords_.clear();
    scopeStack_.clear();
    activeSet_.reset();
    interfaceEqualities_.clear();
    interfaceDisequalities_.clear();
    satFastModel_.reset();  // XOLVER_NRA_SUBTROPICAL
    linRefineRound_ = 0;  // XOLVER_NRA_LINEARIZE: restart refinement budget
    // XOLVER_NRA_PREELIM: the reduced core holds no cross-search state (rebuilt
    // per solve), but drop it so a reset releases the libpoly backend too.
    preElimCore_.reset();
    preElimAlgebra_.reset();
    cacBackend_.reset();   // XOLVER_NRA_CAC: release the CAC libpoly backend
}

void NraSolver::assertLit(const TheoryAtomRecord& atom, bool value,
                          int level, SatLit reason) {
    // Facade-level dedup: same polarity already active → ignore.
    // Opposite polarity is left to the engine's defense-in-depth check.
    if (activeSet_.contains(reason)) {
        return;
    }
    activeSet_.insert(reason);
    satFastModel_.reset();  // XOLVER_NRA_SUBTROPICAL: assignment changed → witness stale

    size_t oldSize = activeLits_.size();
    activeLits_.push_back(reason);
    trail_.push_back({level, oldSize});
    // XOLVER_NRA_LINEARIZE: capture full record (one per assertLit, kept aligned
    // with activeLits_/presolveConstraints_ via the same resize() in backtrack/pop).
    activeRecords_.push_back({reason, atom, value});

    const auto* payload = std::get_if<PolynomialAtomPayload>(&atom.payload);
    if (!payload) {
        // Payload mismatch is an internal routing error, NOT a theory conflict.
        // Engine will see this as unsupported and return Unknown.
        presolveConstraints_.push_back({NullPoly, Relation::Eq, reason});  // keep aligned
        engine_.reset();
        return;
    }

    // Algebraic RHS is not representable in the rational polynomial kernel;
    // it never arises from rational inputs. Treat as unsupported → Unknown.
    auto rhsQ = payload->rhs.tryAsRational();
    if (!rhsQ) {
        presolveConstraints_.push_back({NullPoly, Relation::Eq, reason});  // keep aligned
        engine_.reset();
        return;
    }

    Relation rel = value ? payload->rel : negateRelation(payload->rel);
    // Presolve sees the constraint in `p rel 0` form (subtract rhs if present).
    PolyId diff = payload->poly;
    if (*rhsQ != 0) diff = kernel_->sub(payload->poly, kernel_->mkConst(*rhsQ));
    presolveConstraints_.push_back({diff, rel, reason});
    engine_.assertConstraint(payload->poly, rel, reason, level);
}

void NraSolver::onBacktrack(int level) {
    while (!trail_.empty() && trail_.back().level > level) {
        activeLits_.resize(trail_.back().activeSizeBefore);
        trail_.pop_back();
    }
    activeSet_.rebuildFromActive(activeLits_, [](const auto& lit) { return lit; });
    presolveConstraints_.resize(activeLits_.size());
    activeRecords_.resize(activeLits_.size());
    satFastModel_.reset();  // XOLVER_NRA_SUBTROPICAL: assignment changed → witness stale
    engine_.backtrack(level);
    linRefineRound_ = 0;  // XOLVER_NRA_LINEARIZE: restart refinement budget on backtrack
    auto ieIt = std::remove_if(interfaceEqualities_.begin(), interfaceEqualities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceEqualities_.erase(ieIt, interfaceEqualities_.end());
    auto idIt = std::remove_if(interfaceDisequalities_.begin(), interfaceDisequalities_.end(),
        [level](const auto& ie) { return ie.level > level; });
    interfaceDisequalities_.erase(idIt, interfaceDisequalities_.end());
}

// Stage 1: theory-check presolve fixpoint (Caps. 1–5, 7, with Real domain).
// May return a Conflict (UNSAT direction) via exact linear/sign reasoning,
// or a Lemma; it never returns SAT directly. nullopt → continue to CDCAC.
std::optional<TheoryCheckResult> NraSolver::stagePresolve(TheoryLemmaStorage& /*lemmaDb*/,
                                                          TheoryEffort /*effort*/) {
    PresolveEngine presolve(kernel_.get(), /*integerDomain=*/false);
    bool feasible = true;
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) continue;  // non-polynomial placeholder
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) { feasible = false; break; }
        presolve.addAtom(*rp, c.rel, c.reason);
    }
    if (feasible) {
        auto pr = presolve.run();
        if (pr.kind == PresolveResult::Kind::Conflict)
            return TheoryCheckResult::mkConflict(pr.conflict);
        if (pr.kind == PresolveResult::Kind::Lemma)
            return TheoryCheckResult::mkLemma(pr.lemma);
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
    if (std::getenv("XOLVER_NRA_SIGN_REFUTE_DIAG")) {
        std::ofstream st("/tmp/sign_refute.txt", std::ios::app);
        st << "[SIGN-REFUTE] UNSAT cons=" << cs.size() << " clause=" << tc.clause.size() << "\n";
        st.flush();
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
    PresolveEngine presolve(kernel_.get(), /*integerDomain=*/false);
    std::vector<std::optional<RationalPolynomial>> rps;  // cached RationalPolynomial per cstr
    rps.reserve(liveCstrs.size());
    for (const auto& c : liveCstrs) {
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) return std::nullopt;  // cannot reason; defer to plain CDCAC
        presolve.addAtom(*rp, c.rel, c.reason);
        rps.push_back(rp);
    }
    auto pr = presolve.run();
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
            if (std::getenv("XOLVER_NRA_SUBTROP_DIAG")) {
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

// XOLVER_NRA_CAC: conflict-driven single-cell CAC engine (the "real" CDCAC) as
// the primary NRA decision, run BEFORE the Collins buildClosure. A/B control for
// the Collins-vs-CAC differential; promotion to default is decided by that diff.
std::optional<TheoryCheckResult> NraSolver::stageCac(TheoryLemmaStorage& /*lemmaDb*/,
                                                     TheoryEffort effort) {
    if (!enableCac_) return std::nullopt;
    // EFFORT SCHEDULE (validated by the Collins-vs-CAC A/B + endorsed design):
    //   Standard effort → cheap engines (Collins as cheap CAD, linearized checks);
    //   Full effort     → the heavy CAC/Lazard hard path (this stage), then Collins
    //                     as fallback on CAC-Unknown (stageCdcac runs at all efforts).
    // So in the hybrid CAC runs ONLY at Full: it gets first refusal on the hard
    // cases Collins times out on, while Collins disposes of the easy cases cheaply
    // at Standard — running the heavy CAC at every Standard propagation instead
    // STARVES the time budget (50/150 meti-tarski timeouts in the all-efforts A/B).
    // A fair head-to-head still needs CAC at all efforts (else Collins preempts it
    // at Standard and CAC never runs) — that is what XOLVER_NRA_CAC_ONLY enables
    // (CAC at every effort + Collins disabled): CAC-only=95 vs Collins-only=64,
    // 0-unsound, confirming CAC is the stronger engine on the hard path.
    // Two orthogonal differential flags (decoupled so the full schedule matrix
    // A-E is expressible): CAC_ALL_EFFORTS runs CAC at Standard+Full (else Full
    // only); CAC_NO_COLLINS (read in stageCdcac) disables the Collins fallback.
    static const bool cacAllEfforts = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_ALL_EFFORTS");
        if (e && *e && *e != '0') return true;
        const char* o = std::getenv("XOLVER_NRA_CAC_ONLY");   // legacy alias = all-efforts + no-collins
        return o && *o && *o != '0';
    }();
    if (!cacAllEfforts && effort != TheoryEffort::Full) return std::nullopt;
    // COMBINATION-AWARE CAC (XOLVER_NRA_CAC_COMBINATION, default OFF — the UFNRA
    // medal lane; pairs with EQNA who owns the N-O loop). When OFF, CAC stays
    // PURE-NRA: interface (dis)equalities live in engine_ (asserted via
    // assertInterfaceEquality), not presolveConstraints_, so a CAC verdict that
    // ignored them could be wrong → defer to Collins. When ON, we instead lift
    // the interface (dis)eqs into the CAC constraint set below (root/sign-
    // preserving real constraints poly(a)-poly(b) rel 0), so CAC decides under
    // them and its UNSAT conflict carries their reason lits (see below).
    static const bool cacCombination = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_COMBINATION");
        return e && *e && *e != '0';
    }();
    if (!cacCombination &&
        (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty()))
        return std::nullopt;
#ifdef XOLVER_HAS_LIBPOLY
    // Build the constraint set + active reasons + variable order.
    std::vector<CacConstraint> cacCons;
    std::vector<SatLit> activeReasons;
    std::set<VarId> varSet;
    cacCons.reserve(presolveConstraints_.size());
    for (const auto& c : presolveConstraints_) {
        if (c.poly == NullPoly) return std::nullopt;          // non-polynomial ⇒ defer to Collins
        auto rp = RationalPolynomial::fromPolyId(c.poly, *kernel_);
        if (!rp) return std::nullopt;
        for (VarId v : rp->variables()) varSet.insert(v);
        cacCons.push_back({std::move(*rp), c.rel});
        activeReasons.push_back(c.reason);
    }
    // Combination: lift each N-O interface (dis)equality into a CAC constraint,
    // keeping its reason lit aligned in activeReasons (index ⇒ reason). The
    // conversion REUSES the exact path assertInterfaceEquality fed to engine_
    // (PolynomialConverter::convertConstraint → cc.diff rel 0). If a shared term
    // is not NRA-poly-expressible (UF app feeding a real var) → DEFER the whole
    // CAC run to Collins (sound floor: engine_ already has the interface
    // constraints). The unsatCore (origins) machinery then makes the combination
    // conflict include exactly the interface lits that participated.
    if (cacCombination) {
        auto liftIface = [&](const std::vector<InterfaceEq>& ifaces, Relation rel) -> bool {
            for (const auto& e : ifaces) {
                if (!sharedTermRegistry_ || !coreIr_ || !converter_) return false;
                const auto* stA = sharedTermRegistry_->get(e.a);
                const auto* stB = sharedTermRegistry_->get(e.b);
                if (!stA || !stB) return false;
                auto cc = converter_->convertConstraint(stA->coreExpr, stB->coreExpr, rel, *coreIr_);
                if (cc.status == PolyConstraintStatus::Tautology) continue;   // adds nothing
                if (cc.status == PolyConstraintStatus::Conflict) return false; // constant clash → defer (engine_ caught it at assert)
                if (!cc.isConstraint()) return false;                         // not poly-expressible → defer
                auto rp = RationalPolynomial::fromPolyId(cc.diff, *kernel_);
                if (!rp) return false;
                for (VarId v : rp->variables()) varSet.insert(v);
                cacCons.push_back({std::move(*rp), rel});
                activeReasons.push_back(e.reason);
            }
            return true;
        };
        if (!liftIface(interfaceEqualities_, Relation::Eq) ||
            !liftIface(interfaceDisequalities_, Relation::Neq))
            return std::nullopt;   // shared term not poly-expressible ⇒ sound defer to Collins
    }
    if (cacCons.empty() || varSet.empty()) return std::nullopt;
    std::vector<VarId> varOrder(varSet.begin(), varSet.end());  // sorted (std::set)

    if (!cacBackend_) cacBackend_ = std::make_unique<LibpolyBackend>(kernel_.get());
    // Wall-clock deadline: in the HYBRID (Collins fallback present) bound CAC@Full
    // to a time-share so a hard covering YIELDS to Collins (Unknown→fallback)
    // rather than grinding to the global timeout and starving it. When CAC is the
    // SOLE engine (XOLVER_NRA_CAC_NO_COLLINS / _ONLY) leave it unbounded (0) and
    // rely on the external timeout. Override via XOLVER_NRA_CAC_DEADLINE_MS.
    static const bool soleEngine = [] {
        const char* n = std::getenv("XOLVER_NRA_CAC_NO_COLLINS");
        const char* o = std::getenv("XOLVER_NRA_CAC_ONLY");
        return (n && *n && *n != '0') || (o && *o && *o != '0');
    }();
    static const long cacDeadlineMs = [] () -> long {
        if (const char* e = std::getenv("XOLVER_NRA_CAC_DEADLINE_MS")) return std::atol(e);
        return 2000;    // hybrid default: 2s CAC@Full share (2s-beats-60s: a hard covering
                        // yields fast to Collins instead of grinding); rest of 1200s is Collins
    }();
    static const bool earlyInfeas = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_EARLY_INFEAS");
        return e && *e && *e != '0';
    }();
    static const bool pruneIntervals = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_PRUNE_INTERVALS");
        return e && *e && *e != '0';
    }();
    CacEngine::Config cfg;
    cfg.deadlineMillis = soleEngine ? 0 : cacDeadlineMs;
    cfg.earlyInfeas = earlyInfeas;
    cfg.pruneIntervals = pruneIntervals;
    CacEngine eng(cacBackend_.get(), kernel_.get(), varOrder, std::move(cacCons), cfg);
    CacResult res = eng.solve();

    const bool diag = std::getenv("XOLVER_NRA_CAC_DIAG") != nullptr;
    if (diag) {
        std::ofstream st("/tmp/cac_diff.txt", std::ios::app);
        st << "[CAC] vars=" << varOrder.size() << " cons=" << presolveConstraints_.size()
           << " verdict=" << (res.status == CacStatus::Sat ? "sat"
                              : res.status == CacStatus::Unsat ? "unsat" : "unknown")
           << " depth=" << eng.maxDepthReached()
           << (res.status == CacStatus::Unknown ? (" reason=" + eng.lastUnknown()) : std::string())
           << "\n";
        st.flush();
    }

    if (res.status == CacStatus::Unsat) {
        // SOUNDNESS FLOOR: CAC's covering is NOT yet per-cell-certified, and the
        // regression suite caught false-UNSAT from it (sat cases nra_014/022/047/
        // 138 — an unverified characterization wrongly declared the covering
        // gap-free; the rational-prefix nullification handling is incomplete).
        // Per the no-UNSAT-from-unverified-characterization rule, do NOT trust
        // CAC-UNSAT: defer to Collins (the validated baseline). UNSAT is re-enabled
        // only once each conflict cell carries an exact, checkable certificate.
        // (CAC's validated-SAT below is still sound and IS returned.)
        // XOLVER_NRA_CAC_TRUST_UNSAT re-enables CAC-UNSAT (for validating the
        // required-coefficients characterization fix before promotion); default
        // OFF = the sound floor.
        static const bool trustUnsat = [] {
            const char* e = std::getenv("XOLVER_NRA_CAC_TRUST_UNSAT");
            return e && *e && *e != '0';
        }();
        if (!trustUnsat) return std::nullopt;   // floor: defer to Collins
        TheoryConflict conflict;
        // CONFLICT MINIMIZATION (XOLVER_NRA_CAC_MIN_CONFLICT, default OFF): use
        // only the reason lits of the constraints that actually delineated the
        // covering (CacResult::unsatCore) instead of the whole asserted set.
        // The sub-conjunction over those constraints is itself UNSAT (the covering
        // proves it), so the learned lemma is sound and much tighter — less SAT-
        // core churn. unsatCore is a conservative superset of the minimal core;
        // an EMPTY core (could-not-attribute) falls back to all reasons (sound).
        // This is ALSO the mechanism the combination conflict will reuse to carry
        // the interface-(dis)eq lits that participated (see CAC.md / task P5).
        static const bool minConflict = [] {
            const char* e = std::getenv("XOLVER_NRA_CAC_MIN_CONFLICT");
            return e && *e && *e != '0';
        }();
        if (minConflict && !res.unsatCore.empty()) {
            std::vector<SatLit> minimized;
            minimized.reserve(res.unsatCore.size());
            for (size_t idx : res.unsatCore)
                if (idx < activeReasons.size()) minimized.push_back(activeReasons[idx]);
            if (!minimized.empty()) conflict.clause = std::move(minimized);
            else conflict.clause = std::move(activeReasons);   // defensive fallback
        } else {
            conflict.clause = std::move(activeReasons);
        }
        return TheoryCheckResult::mkConflict(std::move(conflict));
    }
    if (res.status == CacStatus::Sat) {
        // COMBINATION (v1): a CAC SAT under interface constraints means NRA is
        // consistent with the asserted (dis)eqs, but the N-O layer also needs the
        // shared-term ARRANGEMENT read back (task P5 #43, EQNA-paired). Until that
        // read-back exists, DEFER SAT to Collins (engine_ already holds the
        // interface constraints) rather than return a consistent() that the
        // combination loop cannot turn into an arrangement. The UNSAT direction
        // (the medal win) is handled above and IS returned. Sound: Collins is the
        // validated SAT+arrangement baseline.
        if (cacCombination &&
            (!interfaceEqualities_.empty() || !interfaceDisequalities_.empty()))
            return std::nullopt;
        // Report only an all-rational model (the typed channel is mpq); an
        // algebraic witness ⇒ defer to Collins (still sound). The engine already
        // validated the model against every constraint (invariant 1).
        std::unordered_map<VarId, mpq_class> rationalModel;
        for (size_t i = 0; i < res.model.values.size(); ++i) {
            if (!res.model.values[i].isRational()) return std::nullopt;
            rationalModel.emplace(res.model.varOrder[i], res.model.values[i].rational);
        }
        satFastModel_ = std::move(rationalModel);
        return TheoryCheckResult::consistent();
    }
#endif
    return std::nullopt;  // Unknown / no libpoly ⇒ fall through to Collins
}

// Stage 2: the CDCAC (Collins) engine. Always yields a definite verdict.
std::optional<TheoryCheckResult> NraSolver::stageCdcac(TheoryLemmaStorage& /*lemmaDb*/,
                                                       TheoryEffort /*effort*/) {
    // XOLVER_NRA_CAC_NO_COLLINS (differential): disable the Collins fallback so
    // CAC is the sole engine. Return Unknown (not nullopt) so the solver reports
    // unknown when CAC cannot decide, rather than a default/false verdict.
    static const bool noCollins = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_NO_COLLINS");
        if (e && *e && *e != '0') return true;
        const char* o = std::getenv("XOLVER_NRA_CAC_ONLY");   // legacy alias = all-efforts + no-collins
        return o && *o && *o != '0';
    }();
    if (noCollins) return TheoryCheckResult::unknown("cac-only-collins-disabled");
    return engine_.check();
}

// XOLVER_NRA_LINEARIZE incremental-linearization SAT LOOP (default OFF).
//
// Closes the linearization SAT loop for NRA (mirrors NiaSolver but for reals):
//
//   1. Read the LRA sibling's candidate relaxation model (numericAssignments).
//   2. VALIDATE it exactly: for every active original constraint (linear AND
//      nonlinear) compute the exact kernel sign at that rational point and
//      check the relation holds. If the model is non-empty and ALL hold, the
//      candidate is a genuine NRA model → return consistent() (invariant 1:
//      the verdict is backed by an exact-kernel check, never by the
//      abstraction alone).
//   3. Else REFINE: mirror active linear bounds + emit McCormick/square cuts
//      tangent at the CURRENT model point (model-construction), into lemmaDb.
//   4. LOOP CONTROL: if new cuts were emitted, return ONE as mkLemma (the rest
//      sit in lemmaDb). A Lemma result stops the pipeline BEFORE stageCdcac and
//      the SAT core adds the clause + re-solves, re-invoking the theory next
//      round (contract verified: ArithSolverBase::runReasonerPipeline returns
//      the first non-nullopt; CadicalTheoryPropagator enqueues the lemma clause
//      and re-solves). If the round cap is hit or no new cuts were generated
//      (dedup exhausted) and the model didn't validate, fall through to CDCAC.
//
// All diagnostics go to /tmp/linprobe.txt (CLI stderr is suppressed on the
// worker thread). CDCAC remains the backstop for everything this loop can't
// close. Flag OFF → returns nullopt immediately, identical to before.
std::optional<TheoryCheckResult> NraSolver::stageLinearizeProbe(TheoryLemmaStorage& lemmaDb,
                                                                TheoryEffort /*effort*/) {
    static const bool enabled = [] {
        const char* e = std::getenv("XOLVER_NRA_LINEARIZE");
        return e && (e[0]=='1'||e[0]=='t'||e[0]=='T'||e[0]=='y'||e[0]=='Y');
    }();
    if (!enabled) return std::nullopt;
    if (!registry_ || !linAdapter_) return std::nullopt;

    static const int kRefineCap = [] {
        if (const char* c = std::getenv("XOLVER_NRA_LINEARIZE_CAP")) {
            int v = std::atoi(c);
            if (v > 0) return v;
        }
        return 60;
    }();

    std::ofstream lp("/tmp/linprobe.txt", std::ios::app);

    // Total degree of a polynomial via its monomial decomposition. Returns -1 if
    // the kernel cannot decompose it (e.g. non-integer coefficients).
    auto totalDegree = [&](PolyId p) -> int {
        auto termsOpt = kernel_->terms(p);
        if (!termsOpt) return -1;
        int maxDeg = 0;
        for (const auto& t : *termsOpt) {
            int d = 0;
            for (const auto& pe : t.powers) d += pe.second;
            if (d > maxDeg) maxDeg = d;
        }
        return maxDeg;
    };

    // --- Step 1: read the LRA sibling's candidate relaxation model. ----------
    std::unordered_map<std::string, mpq_class> model;
    bool modelFilled = false;
    if (linearSibling_) {
        auto m = linearSibling_->getModel();
        if (m) {
            for (const auto& [name, rv] : m->numericAssignments) {
                auto q = rv.tryAsRational();
                if (q) model.emplace(name, *q);  // skip algebraic/non-rational
            }
            modelFilled = !model.empty();
        }
    }
    // Diagnostic fingerprint of the BASE (non-aux) var values, to tell whether
    // the candidate model changes across rounds or the loop is stuck.
    mpq_class fp(0);
    int nBase = 0, nNonzeroBase = 0;
    for (const auto& [name, val] : model) {
        if (name.rfind("__nl_aux_", 0) == 0) continue;
        ++nBase;
        if (val != 0) ++nNonzeroBase;
        fp += val * val + val;  // order-independent-ish mix
    }
    if (std::getenv("XOLVER_NRA_LINEARIZE_DUMP") && modelFilled) {
        std::ofstream md("/tmp/linmodel.txt", std::ios::app);
        md << "--- model (nBase=" << nBase << " nNonzeroBase=" << nNonzeroBase
           << " total=" << model.size() << ") ---\n";
        int shown = 0;
        for (const auto& [name, val] : model) {
            if (shown++ >= 40) { md << "...\n"; break; }
            md << "  " << name << " = " << val.get_str() << "\n";
        }
        md.flush();
    }

    // --- Step 2: exact validation of EVERY active original constraint. -------
    // The kernel sgn() requires a COMPLETE assignment (every variable of the
    // polynomial must be present, else libpoly evaluates a non-constant value
    // and the rational-interval path corrupts the heap). Vars absent from the
    // candidate model are treated as 0 for the sign check (validation fallback)
    // by explicitly 0-filling each polynomial's variables. The check is over
    // the rational kernel sign, so a pass is a sound NRA model.
    int validated = 0, total = 0;
    bool allHold = true;
    {
        for (const auto& c : presolveConstraints_) {
            if (c.poly == NullPoly) continue;  // non-polynomial placeholder
            ++total;
            std::unordered_map<std::string, mpq_class> evalModel = model;
            for (const auto& vn : kernel_->variables(c.poly)) {
                evalModel.emplace(vn, mpq_class(0));  // 0-fill absent vars
            }
            int s = kernel_->sgn(c.poly, evalModel);
            bool ok = false;
            switch (c.rel) {
                case Relation::Eq:  ok = (s == 0); break;
                case Relation::Geq: ok = (s >= 0); break;
                case Relation::Leq: ok = (s <= 0); break;
                case Relation::Gt:  ok = (s > 0);  break;
                case Relation::Lt:  ok = (s < 0);  break;
                case Relation::Neq: ok = (s != 0); break;
            }
            if (ok) ++validated;
            else allHold = false;
        }
    }

    if (modelFilled && total > 0 && allHold) {
        lp << "[LINPROBE] round=" << linRefineRound_ << " model=filled"
           << " validated=" << validated << "/" << total
           << " newcuts=0 action=SAT\n";
        lp.flush();
        // Sound: the exact kernel sign validates ALL original constraints at a
        // concrete rational point. consistent() = SAT, stop the pipeline.
        return TheoryCheckResult::consistent();
    }

    // --- Step 3: refine. Mirror linear bounds + emit model-tangent cuts. -----
    std::vector<TheoryLemma> newLemmas;

    {
        std::vector<GenericActiveAssignment> gaas;
        gaas.reserve(activeRecords_.size());
        for (const auto& r : activeRecords_) {
            gaas.push_back({r.lit, r.atom, r.value});
        }
        auto mirrorLemmas = linAdapter_->mirrorActiveLinearBounds(gaas, TheoryId::LRA);
        for (auto& ml : mirrorLemmas) {
            if (!lemmaDb.contains(ml)) {
                lemmaDb.insertIfNew(ml);
                newLemmas.push_back(std::move(ml));
            }
        }
    }

    std::vector<ActiveNiaConstraint> activeNonlinear;
    for (const auto& pc : presolveConstraints_) {
        if (pc.poly == NullPoly) continue;
        if (totalDegree(pc.poly) < 2) continue;   // linear: already mirrored above
        activeNonlinear.push_back({pc.poly, pc.rel, pc.reason});
    }

    int nNonlinearNormalized = 0;
    if (!activeNonlinear.empty()) {
        NiaNormalizer normalizer(*kernel_);
        auto normalizedOpt = normalizer.normalize(activeNonlinear);
        if (normalizedOpt) {
            nNonlinearNormalized = static_cast<int>(normalizedOpt->size());
            // Tangent the cuts at the CURRENT model point so they refine around
            // the candidate (model-construction). When the sibling has no model
            // yet, fall back to the bound-free linearizer (nonneg + abstraction).
            auto lr = modelFilled
                ? linAdapter_->runLinearizerAtModel(*normalizedOpt, model, lemmaDb)
                : linAdapter_->runLinearizer(*normalizedOpt, lemmaDb);
            if (lr.status == LinearizationStatus::Lemma) {
                for (auto& item : lr.lemmas) {
                    if (!lemmaDb.contains(item.lemma)) {
                        lemmaDb.insertIfNew(item.lemma);
                        newLemmas.push_back(item.lemma);
                        if (item.cacheKey) linAdapter_->markEmitted(*item.cacheKey);
                    }
                }
            }
        }
    }

    int nNewCuts = static_cast<int>(newLemmas.size());

    // --- Step 4: loop control. -----------------------------------------------
    if (nNewCuts > 0 && linRefineRound_ < kRefineCap) {
        ++linRefineRound_;
        lp << "[LINPROBE] round=" << linRefineRound_
           << " model=" << (modelFilled ? "filled" : "empty")
           << " validated=" << validated << "/" << total
           << " nonlinearNormalized=" << nNonlinearNormalized
           << " newcuts=" << nNewCuts << " fp=" << fp.get_str() << " action=REFINE\n";
        lp.flush();
        // Return ONE lemma; the rest sit in lemmaDb. A Lemma stops the pipeline
        // before stageCdcac and forces a SAT-core re-solve (deferring CDCAC).
        return TheoryCheckResult::mkLemma(newLemmas.front());
    }

    lp << "[LINPROBE] round=" << linRefineRound_
       << " model=" << (modelFilled ? "filled" : "empty")
       << " validated=" << validated << "/" << total
       << " nonlinearNormalized=" << nNonlinearNormalized
       << " newcuts=" << nNewCuts
       << " fp=" << fp.get_str() << " action=CDCAC (cap=" << kRefineCap << ")\n";
    lp.flush();

    // Refinement exhausted (cap hit or dedup-saturated) and no validated model:
    // fall through to the CDCAC backstop (invariant 1: no unvalidated SAT).
    return std::nullopt;
}


TheoryCheckResult NraSolver::assertInterfaceEquality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {
    if (!sharedTermRegistry_ || !coreIr_ || !converter_)
        return TheoryCheckResult::consistent();
    const auto* stA = sharedTermRegistry_->get(a);
    const auto* stB = sharedTermRegistry_->get(b);
    if (!stA || !stB) return TheoryCheckResult::consistent();

    auto cc = converter_->convertConstraint(stA->coreExpr, stB->coreExpr,
                                            Relation::Eq, *coreIr_);
    if (cc.status == PolyConstraintStatus::Tautology)
        return TheoryCheckResult::consistent();
    if (cc.status == PolyConstraintStatus::Conflict)
        return TheoryCheckResult::mkConflict(TheoryConflict{{reason}});
    if (!cc.isConstraint())
        return TheoryCheckResult::consistent();

    engine_.assertConstraint(cc.diff, Relation::Eq, reason, level);
    interfaceEqualities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

TheoryCheckResult NraSolver::assertInterfaceDisequality(
    SharedTermId a, SharedTermId b, SatLit reason, int level) {
    if (!sharedTermRegistry_ || !coreIr_ || !converter_)
        return TheoryCheckResult::consistent();
    const auto* stA = sharedTermRegistry_->get(a);
    const auto* stB = sharedTermRegistry_->get(b);
    if (!stA || !stB) return TheoryCheckResult::consistent();

    auto cc = converter_->convertConstraint(stA->coreExpr, stB->coreExpr,
                                            Relation::Neq, *coreIr_);
    if (cc.status == PolyConstraintStatus::Tautology)
        return TheoryCheckResult::consistent();
    if (cc.status == PolyConstraintStatus::Conflict)
        return TheoryCheckResult::mkConflict(TheoryConflict{{reason}});
    if (!cc.isConstraint())
        return TheoryCheckResult::consistent();

    engine_.assertConstraint(cc.diff, Relation::Neq, reason, level);
    interfaceDisequalities_.push_back({a, b, reason, level});
    return TheoryCheckResult::consistent();
}

std::vector<TheorySolver::SharedEqualityPropagation>
NraSolver::getDeducedSharedEqualities() {
    return {};
}

std::optional<TheorySolver::TheoryModel> NraSolver::getModel() const {
    // XOLVER_NRA_SUBTROPICAL: if the SAT-fast-path produced a validated witness
    // for the current assignment, report it (the CDCAC engine was bypassed, so
    // its sample is stale/empty). Exact rational values.
    if (satFastModel_) {
        TheoryModel model;
        for (const auto& [v, val] : *satFastModel_) {
            std::string name(kernel_->varName(v));
            model.numericAssignments.insert({name, RealValue::fromMpq(val)});
            model.assignments[std::move(name)] = val.get_str();
        }
        return model;
    }

    auto sampleOpt = engine_.getModel();
    if (!sampleOpt) return std::nullopt;
    const auto& sample = *sampleOpt;

    TheoryModel model;
    for (size_t i = 0; i < sample.varOrder.size(); ++i) {
        VarId v = sample.varOrder[i];
        const auto& val = sample.values[i];
        std::string name(kernel_->varName(v));
        // Typed channel: exact RealValue (rational or algebraic).
        model.numericAssignments.insert({name, engine_.sampleValueToRealValue(val)});
        // Legacy string channel (retained during the funnel migration).
        std::string valueStr;
        if (val.kind == RealAlg::Kind::Rational) {
            valueStr = val.rational.get_str();
        } else {
            // AlgebraicRoot: strict representation with defining polynomial + isolating interval
            valueStr = engine_.formatAlgebraicRoot(val.root);
        }
        model.assignments[std::move(name)] = std::move(valueStr);
    }
    return model;
}

} // namespace xolver
