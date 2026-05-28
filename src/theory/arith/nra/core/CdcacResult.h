#pragma once
#include "theory/arith/nra/core/CdcacCertificate.h"

namespace xolver {

// ------------------------------------------------------------------
// V3: Validation result for certificate validator
// ------------------------------------------------------------------
enum class ValidationStatus : uint8_t {
    Valid,
    Invalid,
    Unknown
};

struct ValidationResult {
    ValidationStatus status = ValidationStatus::Unknown;
    CdcacUnknownReason reason = CdcacUnknownReason::None;
};

// ------------------------------------------------------------------
// V3: Build conflict cell result with optional certified cell
// ------------------------------------------------------------------
struct BuildCellResult {
    BuildCellStatus status = BuildCellStatus::Unknown;
    std::optional<CertifiedCell> conflictCell;
    std::optional<SamplePoint> satSample;
    CdcacUnknownReason unknownReason = CdcacUnknownReason::None;
};

// ------------------------------------------------------------------
// CDCAC result with optional unsat certificate and covering certificate
// ------------------------------------------------------------------
struct CdcacUnsatCertificate {
    Covering covering;
    std::vector<SatLit> reasons;
};

struct CdcacResult {
    CdcacStatus status = CdcacStatus::Unknown;
    std::optional<SamplePoint> model;
    std::optional<CdcacUnsatCertificate> unsat;
    std::optional<CoveringCertificate> coveringCert;
    CdcacUnknownReason unknownReason = CdcacUnknownReason::None;

    static CdcacResult mkSat(SamplePoint m) {
        CdcacResult r;
        r.status = CdcacStatus::Sat;
        r.model = std::move(m);
        return r;
    }
    static CdcacResult mkUnsat(Covering cover, std::vector<SatLit> reasons) {
        CdcacResult r;
        r.status = CdcacStatus::Unsat;
        r.unsat = CdcacUnsatCertificate{std::move(cover), std::move(reasons)};
        return r;
    }
    static CdcacResult mkUnknown(CdcacUnknownReason reason) {
        assert(reason != CdcacUnknownReason::None);
        CdcacResult r;
        r.status = CdcacStatus::Unknown;
        r.unknownReason = reason;
        return r;
    }
};

} // namespace xolver
