#pragma once

#include "theory/arith/logics/nra/core/CdcacTypes.h"
#include <optional>
#include <vector>

namespace xolver {

// ------------------------------------------------------------------
// V9: OMT certificate types
// ------------------------------------------------------------------

enum class OptResultKind : uint8_t {
    AttainedOptimum,
    NonAttainedInfimum,
    Unbounded,
    Unknown
};

struct Objective {
    PolyId poly = NullPoly;   // objective polynomial
    bool minimize = true;     // true = minimize, false = maximize
};

struct ObjectiveCellCertificate {
    Cell cell;
    Objective objective;
    OptResultKind localKind = OptResultKind::Unknown;
    std::optional<RealAlg> boundaryValue;
    std::optional<CoveringCertificate> betterRegionExcluded;
    std::vector<SignInvariantCertificate> objectiveSignOrOrderProofs;
};

struct ObjectiveCertificate {
    Objective objective;
    OptResultKind kind = OptResultKind::Unknown;
    std::optional<SamplePoint> optimizer;
    std::optional<RealAlg> infimum;
    std::optional<CoveringCertificate> betterThanBoundUnsatProof;
    std::vector<ObjectiveCellCertificate> boundaryCertificates;
};

// ------------------------------------------------------------------
// V8: Boolean-aware conflict (post-core)
// ------------------------------------------------------------------

struct BooleanAwareConflict {
    std::vector<SatLit> coreReasons;
    std::vector<AtomId> booleanAtoms;
    std::vector<CertificateReasonLit> theoryReasons;
    std::optional<CoveringCertificate> coveringCert;
};

// ------------------------------------------------------------------
// V10: Transcendental constraint (post-core)
// ------------------------------------------------------------------

enum class TranscendentalKind : uint8_t {
    Sin, Cos, Exp, Log, Pow
};

struct TranscendentalConstraint {
    TranscendentalKind kind;
    PolyId argPoly = NullPoly;
    Relation rel = Relation::Eq;
    mpq_class rhs;
    SatLit reason{0, true};
};

} // namespace xolver
