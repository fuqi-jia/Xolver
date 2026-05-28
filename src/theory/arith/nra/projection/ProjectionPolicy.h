#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"
#include <memory>

namespace xolver {

class AlgebraBackend;

// ------------------------------------------------------------------
// V4: ProjectionPolicy — obligation-bearing operator
// ------------------------------------------------------------------
class ProjectionPolicy {
public:
    virtual ~ProjectionPolicy() = default;

    /**
     * Project input polynomials, eliminating `eliminateVar`.
     * Returns projection polynomials + obligations that must hold for
     * the projection to be valid on `baseCell`.
     */
    virtual PolicyProjectionResult project(
        const ProjectionInput& input,
        const ProjectionContext& ctx) = 0;

    /**
     * Validate that the obligations produced by project() hold on baseCell.
     * Used by the certificate validator (exact algebraic, no sampling).
     */
    virtual ValidationResult validateObligations(
        const PolicyProjectionResult& result,
        const Cell& baseCell,
        AlgebraBackend* algebra) = 0;

    virtual ProjectionPolicyKind kind() const = 0;
};

// ------------------------------------------------------------------
// CollinsConservativePolicy — no reduced-projection side conditions
// ------------------------------------------------------------------
class CollinsConservativePolicy : public ProjectionPolicy {
public:
    PolicyProjectionResult project(
        const ProjectionInput& input,
        const ProjectionContext& ctx) override;

    ValidationResult validateObligations(
        const PolicyProjectionResult& result,
        const Cell& baseCell,
        AlgebraBackend* algebra) override;

    ProjectionPolicyKind kind() const override {
        return ProjectionPolicyKind::CollinsConservative;
    }
};

// ------------------------------------------------------------------
// McCallumReducedPolicy — reduced projection with obligations
// Skeleton: falls back to conservative if obligations cannot be met.
// ------------------------------------------------------------------
class McCallumReducedPolicy : public ProjectionPolicy {
public:
    PolicyProjectionResult project(
        const ProjectionInput& input,
        const ProjectionContext& ctx) override;

    ValidationResult validateObligations(
        const PolicyProjectionResult& result,
        const Cell& baseCell,
        AlgebraBackend* algebra) override;

    ProjectionPolicyKind kind() const override {
        return ProjectionPolicyKind::McCallumReduced;
    }
};

// ------------------------------------------------------------------
// LazardStylePolicy — Lazard-style projection
// Skeleton: falls back to conservative.
// ------------------------------------------------------------------
class LazardStylePolicy : public ProjectionPolicy {
public:
    PolicyProjectionResult project(
        const ProjectionInput& input,
        const ProjectionContext& ctx) override;

    ValidationResult validateObligations(
        const PolicyProjectionResult& result,
        const Cell& baseCell,
        AlgebraBackend* algebra) override;

    ProjectionPolicyKind kind() const override {
        return ProjectionPolicyKind::LazardStyle;
    }
};

// ------------------------------------------------------------------
// ECReducedPolicy — equational-constraint-reduced projection
// Skeleton: requires EquationalConstraintManager to detect active ECs.
// ------------------------------------------------------------------
class ECReducedPolicy : public ProjectionPolicy {
public:
    PolicyProjectionResult project(
        const ProjectionInput& input,
        const ProjectionContext& ctx) override;

    ValidationResult validateObligations(
        const PolicyProjectionResult& result,
        const Cell& baseCell,
        AlgebraBackend* algebra) override;

    ProjectionPolicyKind kind() const override {
        return ProjectionPolicyKind::ECReduced;
    }
};

// ------------------------------------------------------------------
// HybridAdaptivePolicy — tries reduced first, falls back to conservative
// ------------------------------------------------------------------
class HybridAdaptivePolicy : public ProjectionPolicy {
public:
    HybridAdaptivePolicy();
    ~HybridAdaptivePolicy() override;

    PolicyProjectionResult project(
        const ProjectionInput& input,
        const ProjectionContext& ctx) override;

    ValidationResult validateObligations(
        const PolicyProjectionResult& result,
        const Cell& baseCell,
        AlgebraBackend* algebra) override;

    ProjectionPolicyKind kind() const override {
        return ProjectionPolicyKind::HybridAdaptive;
    }

private:
    std::unique_ptr<ProjectionPolicy> reducedPolicy_;
    std::unique_ptr<ProjectionPolicy> conservativePolicy_;
};

} // namespace xolver
