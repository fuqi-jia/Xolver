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
    // Integer-aware CDCAC (XOLVER_NRA_CAC_INT): true when this (sub)result's
    // UNSAT relied on integer-specific exclusion (an integrality/integer-point
    // cell anywhere in its subtree). A parent must NOT generalize such an UNSAT
    // across a real interval that may contain other (untested) integers — it is
    // sound only as a single integer point. Real-only UNSATs keep this false and
    // generalize normally. Propagated up through testAndRecurse.
    bool integralityUsed = false;

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
