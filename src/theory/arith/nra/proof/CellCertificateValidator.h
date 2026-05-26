#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"

namespace zolver {

class AlgebraBackend;

/**
 * V3: CellCertificateValidator — validates sufficiency of runtime certificates.
 *
 * Validates: given reasons + certificates → conflict holds.
 * Does NOT check reason minimality (that is ReasonMinimizer's job).
 *
 * Validation is exact-algebraic. Sampling is NEVER used for soundness proof.
 */
class CellCertificateValidator {
public:
    ValidationResult validateCell(const CellCertificate& cert, AlgebraBackend* algebra);
    ValidationResult validateCovering(const CoveringCertificate& cert, AlgebraBackend* algebra);

private:
    ValidationResult validateAtomConditions(const CellCertificate& cert);
    ValidationResult validateReasonSufficiency(const CellCertificate& cert);
    ValidationResult validateCellGeometry(const CellCertificate& cert);
    ValidationResult validateCoverageGeometry(const CoveringCertificate& cert);
};

} // namespace zolver
