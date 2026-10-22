#include "base/RuntimeConfig.h"
#include "applications/smt/qfnia/NiaLinearDecider.h"
#include "base/EnvParam.h"

#include "applications/smt/common/lia/LiaSolver.h"
#include "algebra/linear/LinearConstraintNormalizer.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "contracts/TheoryAtomTypes.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "base/RealValue.h"
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
    const bool on = xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NIA_LINDECIDE_DIAG");
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

    // Lazily build the embedded bounded LIA search decision. Shares NIA's registry so
    // satVars align. A one-shot check() (no SAT-driven branch loop
    // here) needs the LRA→LIA integrality repair to resolve a fractional
    // relaxation to an integer model in a single call.
    if (!lia_) {
        lia_ = std::make_unique<LiaSolver>();
        lia_->setRegistry(registry);
    }
    // LiaSolver rebuilds active bounds each check, so reset and replay suffice.
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

    // This is an internal theory witness, not the public model serializer.
    // Combination still needs auxiliary values (including extensionality
    // indices), and a user variable may legitimately start with "__".
    // Preserve the complete assignment that was actually validated above.
    return im;
}

}  // namespace xolver
