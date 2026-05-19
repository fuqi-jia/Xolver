#include "theory/arith/nra/projection/ProjectionPolicy.h"
#include "theory/arith/nra/projection/LocalProjection.h"
#include "theory/arith/nra/backend/AlgebraBackend.h"

namespace nlcolver {

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
// LazardStylePolicy (skeleton)
// ============================================================================

PolicyProjectionResult LazardStylePolicy::project(
    const ProjectionInput& input,
    const ProjectionContext& ctx) {

    CollinsConservativePolicy conservative;
    PolicyProjectionResult result = conservative.project(input, ctx);
    result.kind = ProjectionPolicyKind::LazardStyle;
    result.isReduced = false;

    if (result.hasDegeneracy) {
        FallbackCondition fb;
        fb.kind = FallbackCondition::Kind::ReducedNotValid;
        fb.fallbackTo = ProjectionPolicyKind::CollinsConservative;
        fb.reason = result.degeneracyReason;
        result.fallbackCondition = std::move(fb);
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

} // namespace nlcolver
