#pragma once

#include "theory/arith/nra/CdcacTypes.h"
#include "theory/arith/nra/CdcacConstraint.h"
#include "theory/arith/nra/LocalProjection.h"
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
 * V2-7: rational prefix only. Algebraic prefix → Unknown.
 */
class NullificationAnalyzer {
public:
    enum class Action {
        SkipConstraintAsTrue,    // constraint is tautologically satisfied
        ReturnFullLineConflict,  // immediate FullLine conflict
        ContinueNormally,        // proceed with normal specialization
        Unknown                  // cannot determine
    };

    struct Analysis {
        Action action = Action::Unknown;
        CdcacUnknownReason reason = CdcacUnknownReason::None;
        std::optional<Cell> conflictCell;  // for ReturnFullLineConflict
        std::vector<ReasonedPolynomial> replacementPolys;  // for ContinueNormally with replacements
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
     */
    Analysis analyzeProjectionPoly(
        const ReasonedPolynomial& rp,
        const SamplePoint& prefix,
        VarId currentVar);

private:
    AlgebraBackend* algebra_;
};

} // namespace nlcolver
