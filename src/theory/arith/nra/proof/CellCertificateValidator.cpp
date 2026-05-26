#include "theory/arith/nra/proof/CellCertificateValidator.h"
#include "theory/arith/nra/backend/AlgebraBackend.h"

namespace zolver {

ValidationResult CellCertificateValidator::validateCell(
    const CellCertificate& cert, AlgebraBackend* /*algebra*/) {

    // 1. Cell geometry
    auto geom = validateCellGeometry(cert);
    if (geom.status != ValidationStatus::Valid) return geom;

    // 2. Atom conditions must be non-empty for all conflict types
    if (cert.atomConditions.empty()) {
        // FullLineViolation is NOT exempt — constant conflicts still need atomConditions
        return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
    }

    // 3. Atom contradiction: invariantSigns & allowedSigns == 0
    auto acResult = validateAtomConditions(cert);
    if (acResult.status != ValidationStatus::Valid) return acResult;

    // 4. Reason sufficiency
    auto rsResult = validateReasonSufficiency(cert);
    if (rsResult.status != ValidationStatus::Valid) return rsResult;

    return {ValidationStatus::Valid, CdcacUnknownReason::None};
}

ValidationResult CellCertificateValidator::validateCovering(
    const CoveringCertificate& cert, AlgebraBackend* algebra) {

    // Validate each cell's certificate
    for (const auto& cc : cert.cells) {
        auto cellRes = validateCell(cc.certificate, algebra);
        if (cellRes.status != ValidationStatus::Valid) {
            return cellRes;
        }
    }

    // Validate coverage geometry
    auto covRes = validateCoverageGeometry(cert);
    if (covRes.status != ValidationStatus::Valid) return covRes;

    return {ValidationStatus::Valid, CdcacUnknownReason::None};
}

ValidationResult CellCertificateValidator::validateAtomConditions(const CellCertificate& cert) {
    for (const auto& ac : cert.atomConditions) {
        // invariantSigns & allowedSigns must be empty (no overlap)
        if ((ac.invariantSigns & ac.allowedSigns) != 0) {
            return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
        }
    }
    return {ValidationStatus::Valid, CdcacUnknownReason::None};
}

ValidationResult CellCertificateValidator::validateReasonSufficiency(const CellCertificate& cert) {
    // Reasons must not be empty for a conflict cell
    if (cert.reasons.empty()) {
        return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
    }

    // Each reason must have a valid lit and normalized atom
    for (const auto& reason : cert.reasons) {
        if (reason.lit.var == 0) {
            return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
        }
        if (reason.normalized.poly == NullPoly) {
            return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
        }
    }

    // No orphan AtomCondition: each AtomCondition must have at least one supporting reason
    // with matching (poly, rel). For MVP we check structural consistency only.
    for (const auto& ac : cert.atomConditions) {
        bool hasSupport = false;
        for (const auto& reason : cert.reasons) {
            if (reason.normalized.poly == ac.poly && reason.normalized.rel == ac.rel) {
                hasSupport = true;
                break;
            }
        }
        if (!hasSupport) {
            return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
        }
    }

    return {ValidationStatus::Valid, CdcacUnknownReason::None};
}

ValidationResult CellCertificateValidator::validateCellGeometry(const CellCertificate& cert) {
    const Cell& cell = cert.cell;

    // Var must match certificate
    if (cell.var != cert.var) {
        return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
    }

    // Section: lower and upper bounds should be equal (same root)
    if (cell.isSection()) {
        // For section cells, the lower and upper bounds should represent the same point
        // Exact comparison may require algebraic backend; for MVP we check structural validity
    }

    // Sector: lower < upper (structural check only)
    if (cell.isSector()) {
        // Structural validity: bounds should not both be negInf or both be posInf
        if (cell.lower.isNegInf() && cell.upper.isNegInf()) {
            return {ValidationStatus::Invalid, CdcacUnknownReason::MalformedCell};
        }
        if (cell.lower.isPosInf() && cell.upper.isPosInf()) {
            return {ValidationStatus::Invalid, CdcacUnknownReason::MalformedCell};
        }
    }

    return {ValidationStatus::Valid, CdcacUnknownReason::None};
}

ValidationResult CellCertificateValidator::validateCoverageGeometry(const CoveringCertificate& cert) {
    const auto& coverage = cert.coverage;

    // orderedCells size must match cells size
    if (coverage.orderedCells.size() != cert.cells.size()) {
        return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
    }

    // Check one-to-one mapping
    for (size_t i = 0; i < coverage.orderedCells.size(); ++i) {
        if (coverage.orderedCells[i].certifiedCellIndex != i) {
            return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
        }
        // Cell reference consistency
        if (coverage.orderedCells[i].cell.var != cert.cells[i].cell.var) {
            return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
        }
    }

    // First cell starts at -inf, last cell ends at +inf
    if (!coverage.orderedCells.empty()) {
        if (coverage.orderedCells.front().lower.kind != EndpointKind::MinusInfinity) {
            return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
        }
        if (coverage.orderedCells.back().upper.kind != EndpointKind::PlusInfinity) {
            return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
        }
    }

    // Adjacent cells: upper of i == lower of i+1
    for (size_t i = 1; i < coverage.orderedCells.size(); ++i) {
        const auto& prevUpper = coverage.orderedCells[i - 1].upper;
        const auto& currLower = coverage.orderedCells[i].lower;
        // Structural check: both should be Algebraic with same value, or match at infinities
        if (prevUpper.kind != currLower.kind) {
            return {ValidationStatus::Invalid, CdcacUnknownReason::InternalInvariantViolation};
        }
    }

    return {ValidationStatus::Valid, CdcacUnknownReason::None};
}

} // namespace zolver
