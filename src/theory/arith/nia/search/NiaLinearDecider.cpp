#include "theory/arith/nia/search/NiaLinearDecider.h"

#include "theory/arith/lia/LiaSolver.h"
#include "theory/arith/linear/LinearConstraintNormalizer.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "util/RealValue.h"
#include <cstdio>
#include <cstdlib>

namespace xolver {

namespace {
// Evaluate `val rel 0`.
bool evalRelZero(const mpq_class& val, Relation rel) {
    switch (rel) {
        case Relation::Eq:  return val == 0;
        case Relation::Neq: return val != 0;
        case Relation::Leq: return val <= 0;
        case Relation::Geq: return val >= 0;
        case Relation::Lt:  return val < 0;
        case Relation::Gt:  return val > 0;
    }
    return false;
}
}  // namespace

static bool linDeciderDiag() {
    static const bool on = std::getenv("XOLVER_NIA_LINDECIDE_DIAG") != nullptr;
    return on;
}

NiaLinearDecider::NiaLinearDecider() = default;
NiaLinearDecider::~NiaLinearDecider() = default;

std::optional<IntegerModel> NiaLinearDecider::decide(
    TheoryAtomRegistry* registry,
    PolynomialKernel& kernel,
    const std::vector<NormalizedNiaConstraint>& normalized,
    const IntegerModelValidator& validator,
    std::optional<TheoryConflict>* outConflict) {
    if (!registry) return std::nullopt;

    // Lazily build the embedded complete-LIA decision. Shares NIA's registry so
    // satVars align. Repair ON: a one-shot check() (no SAT-driven branch loop
    // here) needs the LRA→LIA integrality repair to resolve a fractional
    // relaxation to an integer model in a single call.
    if (!lia_) {
        lia_ = std::make_unique<LiaSolver>();
        lia_->setRegistry(registry);
        lia_->setRepairEnabled(true);
    }
    // LiaSolver full-rebuilds each check by default ⇒ reset + replay is correct.
    lia_->reset();

    // Feed the COMPLETE normalized constraint set (not the SAT trail atoms). The
    // trail is only the asserted atoms; NIA's `normalized_` additionally carries
    // the definitional/derived constraints — crucially the mod/div linkage (e.g.
    // r = Σ − 2^32·q) — without which LIA would solve an under-constrained system
    // and return an invalid over-approximate model. Each NormalizedNiaConstraint
    // is already `poly rel 0` (effective relation, denominators cleared); convert
    // it to LinearAtomPayload and assert it TRUE into the embedded LIA. A
    // nonlinear residual (fromPolynomialZero → nullopt) makes us BAIL: claiming
    // SAT while dropping a constraint would be unsound.
    SatVar synthVar = 1;
    for (const auto& c : normalized) {
        auto zlc = LinearConstraintNormalizer::fromPolynomialZero(
            kernel, c.poly, c.rel, SortKind::Int);
        if (!zlc) return std::nullopt;    // nonlinear term → bail
        LinearAtomSpec spec = LinearConstraintNormalizer::toLinearAtomSpec(*zlc);
        TheoryAtomRecord rec;
        rec.satVar = synthVar++;          // unique per constraint (LIA dedup key)
        rec.theory = TheoryId::LIA;
        rec.isDynamic = false;
        rec.exprId = 0;
        rec.payload = LinearAtomPayload{spec.lhs, spec.rel,
                                        RealValue::fromMpq(spec.rhs)};
        lia_->assertLit(rec, /*value=*/true, /*level=*/0, c.reason);
    }

    // Drive a complete integer solve (LP + repair + branch-and-bound). Returns
    // the COMPLETE assignment (including NIA's "__nlc_*" mod/div aux vars) so the
    // exact re-validation below can evaluate every normalized constraint — those
    // constraints reference the aux vars, and an incomplete assignment both
    // falsifies the equality linkage AND sends libpoly down its heap-unsafe
    // interval-approximation path.
    auto full = lia_->findIntegerModel(/*nodeCap=*/4000, outConflict);
    if (linDeciderDiag())
        std::fprintf(stderr, "[LINDECIDE] findIntegerModel=%s conflict=%s normalized=%zu\n",
                     full ? "yes" : "NO",
                     (outConflict && *outConflict) ? "yes" : "no", normalized.size());
    if (!full) return std::nullopt;

    IntegerModel im;
    for (const auto& [name, rv] : full->numericAssignments) {
        auto q = rv.tryAsRational();
        if (!q) return std::nullopt;                  // algebraic ⇒ not a LIA model
        if (q->get_den() != 1) return std::nullopt;   // fractional ⇒ not integer
        im[name] = q->get_num();
    }
    // Any normalized variable LIA never bounded is genuinely free ⇒ 0 is fine
    // (no equality forces it, or it would have appeared in the model).
    for (const auto& c : normalized)
        for (const auto& v : kernel.variables(c.poly))
            im.emplace(v, mpz_class(0));
    if (im.empty()) return std::nullopt;

    // Exact re-validation against NIA's own normalized constraints (invariant 1:
    // a SAT verdict is backed by a validator pass — defense in depth even though
    // the embedded LIA decision is itself exact and complete).
    auto vr = validator.validate(im, normalized);
    if (linDeciderDiag())
        std::fprintf(stderr, "[LINDECIDE] model=%zu vars validate=%d (0=Valid) normalized=%zu\n",
                     im.size(), (int)vr, normalized.size());
    if (vr != IntegerModelValidator::Result::Valid)
        return std::nullopt;

    // Return only the user-facing variables (strip the "__"-prefixed aux vars).
    IntegerModel out;
    for (const auto& [name, val] : im)
        if (!(name.size() >= 2 && name[0] == '_' && name[1] == '_'))
            out.emplace(name, val);
    if (out.empty()) return std::nullopt;
    return out;
}

void NiaLinearDecider::collectLinearProp(
    TheoryAtomRegistry* registry,
    PolynomialKernel& kernel,
    const std::vector<NormalizedNiaConstraint>& normalized,
    const std::function<bool(SatVar)>& isAssigned,
    const std::function<bool(SatLit)>& litIsTrue,
    std::optional<TheoryConflict>* outConflict,
    std::vector<TheoryLemma>* outEntailments,
    std::unordered_set<uint64_t>* emittedKeys,
    size_t maxEmit) {
    if (!registry) return;

    // Build the embedded simplex from the current normalized set, exactly as
    // decide() does, but solve the ROOT LP only (nodeCap = 0): we want
    // feasibility + the pivoted tableau for proveFixedValue, NOT a full integer
    // model (no branch-and-bound — this runs at Standard effort per cb_propagate).
    if (!lia_) {
        lia_ = std::make_unique<LiaSolver>();
        lia_->setRegistry(registry);
        lia_->setRepairEnabled(true);
    }
    lia_->reset();
    for (const auto& c : normalized) {
        auto zlc = LinearConstraintNormalizer::fromPolynomialZero(
            kernel, c.poly, c.rel, SortKind::Int);
        if (!zlc) return;   // nonlinear residual → cannot reason; bail (no claim)
        LinearAtomSpec spec = LinearConstraintNormalizer::toLinearAtomSpec(*zlc);
        // Sign-canonicalize so complementary inequalities (x≤y and y≤x) feed the
        // SAME aux var → their bounds collapse and pin the difference.
        LinearConstraintNormalizer::canonicalizeSign(spec.lhs, spec.rel, spec.rhs);
        TheoryAtomRecord rec;
        rec.satVar = 1;                 // synthetic — only the reason matters
        rec.theory = TheoryId::LIA;
        rec.isDynamic = false;
        rec.exprId = 0;
        rec.payload = LinearAtomPayload{spec.lhs, spec.rel,
                                        RealValue::fromMpq(spec.rhs)};
        lia_->assertLit(rec, /*value=*/true, /*level=*/0, c.reason);
    }

    // Root LP only. If the relaxation is infeasible, findIntegerModel sets
    // *outConflict to a Farkas conflict over the real asserted `reason` literals.
    std::optional<TheoryConflict> conflict;
    lia_->findIntegerModel(/*nodeCap=*/0, &conflict);
    if (conflict) {
        // Soundness firewall: only surface the conflict if every reason literal
        // is currently true on the trail (defends against any stale reason).
        bool allLive = true;
        for (const auto& lit : conflict->clause)
            if (!litIsTrue(lit)) { allLive = false; break; }
        if (allLive && outConflict) *outConflict = std::move(conflict);
        return;   // infeasible — entailments are moot
    }

    if (!outEntailments) return;

    static const bool diag = std::getenv("XOLVER_NIA_LINPROP_DIAG") != nullptr;
    size_t nArith = 0, nUnassigned = 0, nFormPinned = 0, emitted = 0;

    // Scan registry for UNASSIGNED arithmetic atoms whose linear FORM is pinned
    // to a fixed value by the simplex → their truth value is forced (this
    // captures variable–variable equalities like `x - y = 0`, not just constant
    // pins). Emit each as a fixed-value entailment over the REAL registry satVar.
    for (const auto& rec : registry->records()) {
        if (emitted >= maxEmit) break;

        // Resolve the atom to a ZeroLinearConstraint (expr rel 0) for both poly
        // and linear payloads.
        std::optional<ZeroLinearConstraint> zlc;
        if (const auto* lp = std::get_if<LinearAtomPayload>(&rec.payload)) {
            if (rec.theory != TheoryId::LIA && rec.theory != TheoryId::NIA) continue;
            auto rhsQ = lp->rhs.tryAsRational();
            if (!rhsQ) continue;
            ZeroLinearConstraint z;
            for (const auto& t : lp->lhs.terms)
                z.expr.terms.push_back({t.first, t.second});
            z.expr.constant = -*rhsQ;     // (Σ coeff*var) rel rhs  ⟺  (Σ - rhs) rel 0
            z.rel = lp->rel;
            zlc = std::move(z);
        } else if (const auto* pp = std::get_if<PolynomialAtomPayload>(&rec.payload)) {
            if (rec.theory != TheoryId::NIA && rec.theory != TheoryId::LIA) continue;
            auto rhsQ = pp->rhs.tryAsRational();
            if (!rhsQ) continue;
            PolyId p = pp->poly;
            if (*rhsQ != 0) p = kernel.sub(pp->poly, kernel.mkConst(*rhsQ));
            zlc = LinearConstraintNormalizer::fromPolynomialZero(
                kernel, p, pp->rel, SortKind::Int);
            if (!zlc) continue;           // nonlinear atom → cannot evaluate via pins
        } else {
            continue;                      // not an arithmetic bound atom
        }
        ++nArith;
        if (isAssigned(rec.satVar)) continue;   // already decided on the trail
        ++nUnassigned;

        // Pin the FORM `(Σ coeff*var + constant)` = `(lhs - rhs)` with
        // lhs = terms, rhs = -constant.
        LinearFormKey lhsForm;
        for (const auto& t : zlc->expr.terms) lhsForm.terms.push_back({t.var, t.coeff});
        mpq_class rhs = -zlc->expr.constant;
        auto pin = lia_->proveFixedFormValue(lhsForm, rhs);
        if (!pin) continue;               // form not pinned → not forced
        ++nFormPinned;

        // Soundness firewall: every reason must be currently true on the trail.
        bool allLive = true;
        for (const auto& r : pin->second)
            if (!litIsTrue(r)) { allLive = false; break; }
        if (!allLive) continue;

        bool atomTrue = evalRelZero(pin->first, zlc->rel);   // (lhs - rhs) rel 0
        uint64_t key = (static_cast<uint64_t>(rec.satVar) << 1) |
                       (atomTrue ? 1u : 0u);
        if (emittedKeys && !emittedKeys->insert(key).second) continue;

        TheoryLemma lemma;
        lemma.kind = LemmaKind::Entailment;
        for (const auto& r : pin->second) lemma.lits.push_back(r.negated());
        SatLit atomLit{rec.satVar, true};
        lemma.lits.push_back(atomTrue ? atomLit : atomLit.negated());
        outEntailments->push_back(std::move(lemma));
        ++emitted;
    }

    if (diag) {
        std::fprintf(stderr,
            "[LINPROP-scan] records=%zu arith=%zu unassigned=%zu formPinned=%zu emitted=%zu\n",
            registry->records().size(), nArith, nUnassigned, nFormPinned, emitted);
        std::fflush(stderr);
    }
}

}  // namespace xolver
