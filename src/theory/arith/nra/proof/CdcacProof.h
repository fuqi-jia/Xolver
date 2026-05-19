#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"
#include <vector>

namespace nlcolver {

// ------------------------------------------------------------------
// V7: Proof IDs (index-based, serializable)
// ------------------------------------------------------------------
using ProofCoveringId = uint64_t;
constexpr ProofCoveringId NullProofCoveringId = 0;

// ------------------------------------------------------------------
// V7: ProofProjectionStep — one projection operation
// ------------------------------------------------------------------
struct ProofProjectionStep {
    int fromLevel = -1;
    int toLevel = -1;
    VarId eliminatedVar = NullVar;
    std::vector<ReasonedPolynomial> inputPolys;
    std::vector<ReasonedPolynomial> outputPolys;
    ProjectionPolicyKind policyUsed = ProjectionPolicyKind::CollinsConservative;
    std::vector<ProjectionObligation> obligations;
};

// ------------------------------------------------------------------
// V7: SampleSignCertificate — exact sign at sample (for SAT)
// ------------------------------------------------------------------
struct SampleSignCertificate {
    PolyId poly = NullPoly;
    SamplePoint sample;
    Sign sign = Sign::Unknown;
};

// ------------------------------------------------------------------
// V7: CellSignInvariantProof — sign invariance with replayed obligations
// ------------------------------------------------------------------
struct CellSignInvariantProof {
    SignInvariantCertificate invariant;
    std::vector<ProjectionObligation> replayedObligations;
};

// ------------------------------------------------------------------
// V7: ProofCellCertificate — serializable cell certificate
// Key difference from V3: uses ProofCoveringId instead of unique_ptr.
// ------------------------------------------------------------------
struct ProofCellCertificate {
    CellCertificateKind kind = CellCertificateKind::SignInvariantViolation;
    int level = -1;
    VarId var = NullVar;
    Cell cell;
    std::vector<AtomCondition> atomConditions;
    std::vector<CellSignInvariantProof> signProofs;
    std::vector<CertificateReasonLit> reasons;
    std::vector<ProofCoveringId> childCoverings;  // index into CdcacProof.coverings
};

// ------------------------------------------------------------------
// V7: ProofCovering — serializable covering certificate
// ------------------------------------------------------------------
struct ProofCovering {
    ProofCoveringId id = NullProofCoveringId;
    int level = -1;
    VarId var = NullVar;
    Cell parentCell;
    std::vector<ProofCellCertificate> cells;
    std::vector<ReasonedPolynomial> projectionBasis;
    std::vector<ProjectionObligation> projectionObligations;
    CoverageCertificate coverage;
};

// ------------------------------------------------------------------
// V7: CdcacProof — complete external proof artifact
// Value-based, serializable, independent of solver memory layout.
// ------------------------------------------------------------------
struct CdcacProof {
    enum class Kind : uint8_t { SatModel, UnsatCovering };
    Kind kind = Kind::UnsatCovering;

    // For SAT
    std::optional<SamplePoint> model;
    std::vector<SampleSignCertificate> sampleSigns;

    // For UNSAT
    std::vector<ProofCovering> coverings;
    std::vector<ProofProjectionStep> projectionSteps;
    std::vector<CellSignInvariantProof> cellSignProofs;
};

} // namespace nlcolver
