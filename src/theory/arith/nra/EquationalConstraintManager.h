#pragma once

#include "theory/arith/nra/CdcacTypes.h"
#include "theory/arith/nra/CdcacConstraint.h"
#include <vector>
#include <memory>

namespace nlcolver {

class AlgebraBackend;
class ProjectionPolicy;

// ------------------------------------------------------------------
// V4: EquationalConstraintInfo — polarity-normalized EQ only
// ------------------------------------------------------------------
struct EquationalConstraintInfo {
    CertificateReasonLit reason;       // lit + polarity + normalized atom
    NormalizedAtom normalized;         // relation MUST be EQ after polarity normalization
    RationalPolynomial poly;
    int mainLevel = -1;
    bool activeUnderCurrentBranch = false;
};

// ------------------------------------------------------------------
// ActiveConstraintSet — incremental constraint management with lit mapping
// V5 will expand this; V4 keeps a minimal version for EC detection.
// ------------------------------------------------------------------
struct ActiveConstraintSet {
    std::vector<CdcacConstraint> constraints;
    std::vector<EquationalConstraintInfo> equationalConstraints;
    int decisionLevel = 0;
};

// ------------------------------------------------------------------
// V4: EquationalConstraintManager — detects and manages active ECs
// ------------------------------------------------------------------
class EquationalConstraintManager {
public:
    explicit EquationalConstraintManager(AlgebraBackend* algebra);

    /**
     * Detect active equational constraints from the current constraint set.
     * Only constraints whose normalized relation is EQ are considered.
     * Hard rule: p != 0 (true) is a disequality, not an EC.
     *            ¬(p != 0) (true) normalizes to p = 0 and CAN be an EC.
     */
    std::vector<EquationalConstraintInfo> detectActiveECs(
        const ActiveConstraintSet& constraints);

    /**
     * Choose a projection policy based on detected ECs.
     * If no ECs are found, returns CollinsConservativePolicy.
     * If ECs are found but EC-reduced is not yet fully wired, falls back
     * to conservative with a fallback condition.
     */
    std::unique_ptr<ProjectionPolicy> choosePolicy(
        const std::vector<EquationalConstraintInfo>& ecs);

    /**
     * Validate that reduced projection is valid given the ECs.
     * V4 skeleton: always returns Valid for conservative; Unknown for reduced.
     */
    ValidationResult validateReducedProjection(
        const std::vector<EquationalConstraintInfo>& ecs,
        const PolicyProjectionResult& projResult,
        const Cell& baseCell);

private:
    AlgebraBackend* algebra_;
};

} // namespace nlcolver
