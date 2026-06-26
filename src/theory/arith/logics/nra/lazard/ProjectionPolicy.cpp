#include "theory/arith/logics/nra/lazard/ProjectionPolicy.h"
#include "theory/arith/logics/nra/lazard/LocalProjection.h"
#include "theory/arith/logics/nra/lazard/LazardProjectionOperator.h"
#include "theory/arith/logics/nra/backend/AlgebraBackend.h"

#include <algorithm>

namespace xolver {

// ============================================================================
// CollinsConservativePolicy
// ============================================================================

PolicyProjectionResult CollinsConservativePolicy::project(
    const ProjectionInput& input,
    const ProjectionContext& /*ctx*/) {

    LocalProjectionEngine engine;
    LocalProjectionResult local = engine.project(input.polys, input.eliminateVar);

    PolicyProjectionResult result;
    result.kind = ProjectionPolicyKind::CollinsConservative;
    result.projectionPolys = std::move(local.polys);
    result.hasDegeneracy = local.hasDegeneracy;
    result.degeneracyReason = local.degeneracyReason;
    result.isReduced = false;
    // Conservative projection requires no side-condition obligations.
    // The validator checks projection set completeness instead.
    return result;
}

ValidationResult CollinsConservativePolicy::validateObligations(
    const PolicyProjectionResult& /*result*/,
    const Cell& /*baseCell*/,
    AlgebraBackend* /*algebra*/) {
    // Conservative projection has no per-projection obligations.
    // Completeness is checked by the validator independently.
    return ValidationResult{ValidationStatus::Valid, CdcacUnknownReason::None};
}

// ============================================================================
// McCallumReducedPolicy (skeleton)
// ============================================================================

PolicyProjectionResult McCallumReducedPolicy::project(
    const ProjectionInput& input,
    const ProjectionContext& ctx) {

    // V4 skeleton: attempt McCallum reduced projection.
    // For now: run conservative, then tag as "attempted reduced" with empty
    // obligations. Full implementation requires coefficient/discriminant/resultant
    // non-zero checks on baseCell.
    CollinsConservativePolicy conservative;
    PolicyProjectionResult result = conservative.project(input, ctx);

    result.kind = ProjectionPolicyKind::McCallumReduced;
    result.isReduced = false;  // not yet truly reduced in V4

    // If degeneracy occurs, mark fallback.
    if (result.hasDegeneracy) {
        FallbackCondition fb;
        fb.kind = FallbackCondition::Kind::ReducedNotValid;
        fb.fallbackTo = ProjectionPolicyKind::CollinsConservative;
        fb.reason = result.degeneracyReason;
        result.fallbackCondition = std::move(fb);
    }

    return result;
}

ValidationResult McCallumReducedPolicy::validateObligations(
    const PolicyProjectionResult& /*result*/,
    const Cell& /*baseCell*/,
    AlgebraBackend* /*algebra*/) {
    // V4 skeleton: McCallum obligations (discriminants non-zero, resultants non-zero,
    // leading coefficients non-zero) are not yet fully wired.
    return ValidationResult{ValidationStatus::Valid, CdcacUnknownReason::None};
}

// ============================================================================
// LazardStylePolicy — real Lazard projection operator
// ============================================================================

namespace {

// Map a Lazard projection incompleteness reason onto the CDCAC unknown-reason
// taxonomy. An incomplete Lazard step never stands alone (we fall back to the
// Collins-conservative projection); the reason is recorded for diagnostics.
CdcacUnknownReason lazardReasonToCdcac(LazardIncompleteReason r) {
    switch (r) {
        case LazardIncompleteReason::ProjectionKernelFailure:
            return CdcacUnknownReason::SquarefreeFailed;
        case LazardIncompleteReason::ProjectionBudgetExceeded:
            return CdcacUnknownReason::ResourceBudgetExceeded;
        case LazardIncompleteReason::None:
        default:
            return CdcacUnknownReason::None;
    }
}

// Merge + dedup the reason literals of all input polynomials that contain the
// eliminated variable; the Lazard operator does not thread per-item reasons, so
// (mirroring the Collins resultant-reason merge) every projected polynomial
// inherits the conservative union of the contributing constraints' reasons. A
// superset reason is always sound for explanation.
std::vector<SatLit> mergeReasonsContaining(
    const std::vector<ReasonedPolynomial>& polys, VarId v) {
    std::vector<SatLit> merged;
    for (const auto& rp : polys) {
        if (!rp.poly.contains(v)) continue;
        merged.insert(merged.end(), rp.reasons.begin(), rp.reasons.end());
    }
    std::sort(merged.begin(), merged.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    merged.erase(std::unique(merged.begin(), merged.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), merged.end());
    return merged;
}

}  // namespace

PolicyProjectionResult LazardStylePolicy::project(
    const ProjectionInput& input,
    const ProjectionContext& ctx) {

    // Extract the polynomial set for the Lazard operator. The operator itself
    // filters to those containing the eliminated variable and carries the rest
    // down implicitly (the closure / parent level still sees them via the
    // original constraint set), so we pass them all through.
    std::vector<RationalPolynomial> E;
    E.reserve(input.polys.size());
    for (const auto& rp : input.polys) {
        if (rp.poly.isZero()) continue;
        E.push_back(rp.poly);
    }

    LazardProjectionConfig cfg;  // default psc budget (maxMatrixDim)
    LazardOpResult op = lazardProjectStep(E, input.eliminateVar, cfg);

    // SOUNDNESS FLOOR: an incomplete Lazard step (kernel failure / budget) must
    // NEVER stand alone as a projection set — a missing boundary polynomial can
    // drop a satisfiable region. Fall back to the Collins-conservative
    // projection so the projection set is at least as rich as the baseline.
    if (!op.complete) {
        CollinsConservativePolicy conservative;
        PolicyProjectionResult result = conservative.project(input, ctx);
        result.kind = ProjectionPolicyKind::LazardStyle;
        result.isReduced = false;

        FallbackCondition fb;
        fb.kind = FallbackCondition::Kind::ReducedNotValid;
        fb.fallbackTo = ProjectionPolicyKind::CollinsConservative;
        fb.reason = lazardReasonToCdcac(op.reason);
        result.fallbackCondition = std::move(fb);
        // Surface the degeneracy reason for diagnostics without clobbering the
        // (already-populated) Collins polys.
        if (result.degeneracyReason == CdcacUnknownReason::None)
            result.degeneracyReason = fb.reason;
        return result;
    }

    PolicyProjectionResult result;
    result.kind = ProjectionPolicyKind::LazardStyle;
    result.isReduced = false;

    std::vector<SatLit> reasons = mergeReasonsContaining(input.polys, input.eliminateVar);

    // Map the Lazard items into lower-level projection polynomials, mirroring the
    // Collins output shape: only polynomials that no longer contain the
    // eliminated variable (and are non-constant) are projection output. The
    // SquarefreeFactor items remain in the eliminated variable — they are the
    // current-level boundary factors used by the lifter, NOT projection output —
    // so they are intentionally skipped here.
    for (const auto& it : op.items) {
        if (it.op == LazardProjectionOpKind::SquarefreeFactor) continue;
        if (it.poly.isZero() || it.poly.isConstant()) continue;
        if (it.poly.contains(input.eliminateVar)) continue;
        result.projectionPolys.push_back(
            ReasonedPolynomial{it.poly, PolyRole::ProjectionPolynomial, reasons});
    }

    return result;
}

ValidationResult LazardStylePolicy::validateObligations(
    const PolicyProjectionResult& /*result*/,
    const Cell& /*baseCell*/,
    AlgebraBackend* /*algebra*/) {
    return ValidationResult{ValidationStatus::Valid, CdcacUnknownReason::None};
}

// ============================================================================
// ECReducedPolicy (skeleton)
// ============================================================================

PolicyProjectionResult ECReducedPolicy::project(
    const ProjectionInput& input,
    const ProjectionContext& ctx) {

    CollinsConservativePolicy conservative;
    PolicyProjectionResult result = conservative.project(input, ctx);
    result.kind = ProjectionPolicyKind::ECReduced;
    result.isReduced = false;

    if (result.hasDegeneracy) {
        FallbackCondition fb;
        fb.kind = FallbackCondition::Kind::ECNotApplicable;
        fb.fallbackTo = ProjectionPolicyKind::CollinsConservative;
        fb.reason = result.degeneracyReason;
        result.fallbackCondition = std::move(fb);
    }

    return result;
}

ValidationResult ECReducedPolicy::validateObligations(
    const PolicyProjectionResult& /*result*/,
    const Cell& /*baseCell*/,
    AlgebraBackend* /*algebra*/) {
    return ValidationResult{ValidationStatus::Valid, CdcacUnknownReason::None};
}

// ============================================================================
// HybridAdaptivePolicy
// ============================================================================

HybridAdaptivePolicy::HybridAdaptivePolicy()
    : reducedPolicy_(std::make_unique<McCallumReducedPolicy>()),
      conservativePolicy_(std::make_unique<CollinsConservativePolicy>()) {}

HybridAdaptivePolicy::~HybridAdaptivePolicy() = default;

PolicyProjectionResult HybridAdaptivePolicy::project(
    const ProjectionInput& input,
    const ProjectionContext& ctx) {

    // Try reduced first
    PolicyProjectionResult reduced = reducedPolicy_->project(input, ctx);

    // If reduced succeeds without degeneracy and without fallback, use it.
    if (!reduced.hasDegeneracy && !reduced.fallbackCondition.has_value()) {
        reduced.kind = ProjectionPolicyKind::HybridAdaptive;
        return reduced;
    }

    // Fallback to conservative
    PolicyProjectionResult conservative = conservativePolicy_->project(input, ctx);
    conservative.kind = ProjectionPolicyKind::HybridAdaptive;

    // Preserve fallback info from reduced attempt
    if (reduced.fallbackCondition.has_value()) {
        conservative.fallbackCondition = std::move(reduced.fallbackCondition);
    }

    return conservative;
}

ValidationResult HybridAdaptivePolicy::validateObligations(
    const PolicyProjectionResult& result,
    const Cell& baseCell,
    AlgebraBackend* algebra) {

    // If the result came from a fallback, validate as conservative.
    // Otherwise validate as reduced.
    if (result.fallbackCondition.has_value()) {
        return conservativePolicy_->validateObligations(result, baseCell, algebra);
    }
    return reducedPolicy_->validateObligations(result, baseCell, algebra);
}

} // namespace xolver
