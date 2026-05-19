#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include "theory/arith/nra/projection/LocalProjection.h"
#include <optional>

namespace nlcolver {

class AlgebraBackend;

/**
 * NullificationAnalyzer: detect and classify polynomial nullification.
 *
 * Two entry points:
 * 1. analyzeConstraint: check if a constraint polynomial vanishes at prefix.
 * 2. analyzeProjectionPoly: check if a projection polynomial vanishes after specialization.
 *
 * V4: produces NullificationRepair with verifiable obligations where possible.
 */
class NullificationAnalyzer {
public:
    enum class Action {
        SkipConstraintAsTrue,    // constraint is tautologically satisfied
        ReturnFullLineConflict,  // immediate FullLine conflict
        ContinueNormally,        // proceed with normal specialization
        NeedsRepair,             // V4: nullification can be repaired with obligations
        Unknown                  // cannot determine
    };

    struct Analysis {
        Action action = Action::Unknown;
        CdcacUnknownReason reason = CdcacUnknownReason::None;
        std::optional<Cell> conflictCell;  // for ReturnFullLineConflict
        std::vector<ReasonedPolynomial> replacementPolys;  // for ContinueNormally with replacements
        NullificationRepair repair;  // V4: for NeedsRepair
    };

    explicit NullificationAnalyzer(AlgebraBackend* algebra);

    /**
     * Analyze a constraint for nullification at the given prefix.
     */
    Analysis analyzeConstraint(
        const CdcacConstraint& c,
        const SamplePoint& prefix,
        VarId currentVar);

    /**
     * Analyze a projection polynomial after specialization.
     * V4 skeleton: returns ContinueNormally or Unknown.
     */
    Analysis analyzeProjectionPoly(
        const ReasonedPolynomial& rp,
        const SamplePoint& prefix,
        VarId currentVar);

    /**
     * V4: Attempt to build a certified repair for a nullified polynomial.
     * Returns a NullificationRepair with obligations, or Unknown if not possible.
     */
    NullificationRepair attemptRepair(
        const ReasonedPolynomial& rp,
        const SamplePoint& prefix,
        VarId currentVar);

private:
    AlgebraBackend* algebra_;
};

} // namespace nlcolver
