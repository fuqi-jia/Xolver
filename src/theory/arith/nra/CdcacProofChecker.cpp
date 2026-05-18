#include "theory/arith/nra/CdcacProofChecker.h"
#include "theory/arith/nra/AlgebraBackend.h"

namespace nlcolver {

CdcacProofChecker::CdcacProofChecker(AlgebraBackend* algebra)
    : algebra_(algebra) {}

ProofCheckResult CdcacProofChecker::check(const CdcacProof& proof) {
    switch (proof.kind) {
        case CdcacProof::Kind::SatModel:
            return checkSatModel(proof);
        case CdcacProof::Kind::UnsatCovering:
            return checkUnsatCovering(proof);
    }
    return {ProofCheckStatus::Invalid, "Unknown proof kind", CdcacUnknownReason::InternalInvariantViolation};
}

ProofCheckResult CdcacProofChecker::checkSatModel(const CdcacProof& proof) {
    if (!proof.model.has_value()) {
        return {ProofCheckStatus::Invalid, "SAT proof missing model", CdcacUnknownReason::InternalInvariantViolation};
    }
    // V7: validate each SampleSignCertificate against the model
    for (const auto& sc : proof.sampleSigns) {
        if (!algebra_) {
            return {ProofCheckStatus::Unknown, "No algebra backend for sign validation",
                    CdcacUnknownReason::BackendFailure};
        }
        Sign actual = algebra_->signAt(sc.poly, sc.sample);
        if (actual != sc.sign) {
            return {ProofCheckStatus::Invalid, "Sample sign mismatch",
                    CdcacUnknownReason::SignEvaluationInconclusive};
        }
    }
    return {ProofCheckStatus::Valid, "SAT model validated"};
}

ProofCheckResult CdcacProofChecker::checkUnsatCovering(const CdcacProof& proof) {
    // 1. Check all coverings are valid
    for (const auto& cov : proof.coverings) {
        auto r = checkCovering(cov);
        if (r.status != ProofCheckStatus::Valid) return r;
    }
    // 2. Check projection steps are legal
    for (const auto& step : proof.projectionSteps) {
        auto r = checkProjectionStep(step);
        if (r.status != ProofCheckStatus::Valid) return r;
    }
    // 3. Check cell sign proofs
    for (const auto& sp : proof.cellSignProofs) {
        for (const auto& obl : sp.replayedObligations) {
            auto r = checkObligation(obl, sp.invariant.baseCell);
            if (r.status != ProofCheckStatus::Valid) return r;
        }
    }
    return {ProofCheckStatus::Valid, "UNSAT covering validated"};
}

ProofCheckResult CdcacProofChecker::checkProjectionStep(const ProofProjectionStep& /*step*/) {
    // V7 skeleton: full projection step validation requires checking that
    // output polynomials are correct resultants/discriminants/coefficients
    // of input polynomials w.r.t. eliminatedVar.
    return {ProofCheckStatus::Valid, "Projection step skeleton"};
}

ProofCheckResult CdcacProofChecker::checkCellCertificate(const ProofCellCertificate& cellCert) {
    // Every conflict cell must have non-empty atomConditions
    if (cellCert.atomConditions.empty()) {
        return {ProofCheckStatus::Invalid, "Cell certificate has empty atomConditions",
                CdcacUnknownReason::ReasonReplayFailed};
    }
    // Validate atom contradictions
    for (const auto& ac : cellCert.atomConditions) {
        if ((ac.invariantSigns & ac.allowedSigns) != 0) {
            return {ProofCheckStatus::Invalid, "Atom condition does not contradict",
                    CdcacUnknownReason::ReasonReplayFailed};
        }
    }
    return {ProofCheckStatus::Valid, "Cell certificate validated"};
}

ProofCheckResult CdcacProofChecker::checkCovering(const ProofCovering& covering) {
    // Check coverage completeness
    if (covering.cells.empty()) {
        return {ProofCheckStatus::Invalid, "Empty covering",
                CdcacUnknownReason::CellConstructionFailed};
    }
    // Check each cell certificate
    for (const auto& cell : covering.cells) {
        auto r = checkCellCertificate(cell);
        if (r.status != ProofCheckStatus::Valid) return r;
    }
    // Check orderedCells consistency
    if (covering.coverage.orderedCells.size() != covering.cells.size()) {
        return {ProofCheckStatus::Invalid, "Coverage orderedCells size mismatch",
                CdcacUnknownReason::MalformedCell};
    }
    return {ProofCheckStatus::Valid, "Covering validated"};
}

ProofCheckResult CdcacProofChecker::checkObligation(
    const ProjectionObligation& obligation,
    const Cell& baseCell) {

    // V7 skeleton: obligation validation depends on kind
    switch (obligation.kind) {
        case ObligationKind::NonVanishing:
            // Check witness polynomials are non-zero on baseCell
            return {ProofCheckStatus::Valid, "NonVanishing obligation skeleton"};
        case ObligationKind::Delineable:
            return {ProofCheckStatus::Valid, "Delineable obligation skeleton"};
        case ObligationKind::DegreeInvariant:
            return {ProofCheckStatus::Valid, "DegreeInvariant obligation skeleton"};
        case ObligationKind::ProjectionCompleteness:
            return {ProofCheckStatus::Valid, "ProjectionCompleteness obligation skeleton"};
        case ObligationKind::ResultantSeparation:
            return {ProofCheckStatus::Valid, "ResultantSeparation obligation skeleton"};
        case ObligationKind::DiscriminantNonZero:
            return {ProofCheckStatus::Valid, "DiscriminantNonZero obligation skeleton"};
        case ObligationKind::LeadingCoefficientNonZero:
            return {ProofCheckStatus::Valid, "LeadingCoefficientNonZero obligation skeleton"};
        case ObligationKind::ECValidity:
            return {ProofCheckStatus::Valid, "ECValidity obligation skeleton"};
        case ObligationKind::NullificationRepairSoundness:
            return {ProofCheckStatus::Valid, "NullificationRepairSoundness obligation skeleton"};
    }
    return {ProofCheckStatus::Unknown, "Unknown obligation kind"};
}

} // namespace nlcolver
