#pragma once

#include "theory/arith/nra/proof/CdcacProof.h"
#include "theory/arith/nra/core/CdcacTypes.h"
#include <string>

namespace zolver {

class AlgebraBackend;

// ------------------------------------------------------------------
// V7: CdcacProofChecker — independent proof validation
// Runs without solver; validates CdcacProof algebraically.
// ------------------------------------------------------------------
enum class ProofCheckStatus : uint8_t {
    Valid,
    Invalid,
    Unknown
};

struct ProofCheckResult {
    ProofCheckStatus status = ProofCheckStatus::Unknown;
    std::string message;
    CdcacUnknownReason reason = CdcacUnknownReason::None;
};

class CdcacProofChecker {
public:
    explicit CdcacProofChecker(AlgebraBackend* algebra);

    // Validate a complete CdcacProof
    ProofCheckResult check(const CdcacProof& proof);

    // Individual validation steps (exposed for testing/debugging)
    ProofCheckResult checkSatModel(const CdcacProof& proof);
    ProofCheckResult checkUnsatCovering(const CdcacProof& proof);
    ProofCheckResult checkProjectionStep(const ProofProjectionStep& step);
    ProofCheckResult checkCellCertificate(const ProofCellCertificate& cellCert);
    ProofCheckResult checkCovering(const ProofCovering& covering);

    // Validate obligations per kind
    ProofCheckResult checkObligation(
        const ProjectionObligation& obligation,
        const Cell& baseCell);

private:
    AlgebraBackend* algebra_;
};

} // namespace zolver
