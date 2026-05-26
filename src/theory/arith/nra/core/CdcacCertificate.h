#pragma once
#include "theory/arith/nra/core/CdcacCell.h"

namespace zolver {

// ------------------------------------------------------------------
// V3: Normalized atom representation for certificates
// ------------------------------------------------------------------
struct NormalizedAtom {
    PolyId poly = NullPoly;
    Relation rel = Relation::Eq;
};

// ------------------------------------------------------------------
// V3: Bitflag sign for certificate invariant sets
// ------------------------------------------------------------------
enum class AtomSign : uint8_t {
    Neg  = 1,
    Zero = 2,
    Pos  = 4
};

using SignSet = uint8_t;

constexpr SignSet atomSignBit(AtomSign s) {
    return static_cast<SignSet>(s);
}

constexpr SignSet makeSignSet(std::initializer_list<AtomSign> signs) {
    SignSet r = 0;
    for (auto s : signs) r |= atomSignBit(s);
    return r;
}

inline SignSet signSetFromRelation(Relation rel) {
    switch (rel) {
        case Relation::Lt:  return makeSignSet({AtomSign::Neg});
        case Relation::Leq: return makeSignSet({AtomSign::Neg, AtomSign::Zero});
        case Relation::Eq:  return makeSignSet({AtomSign::Zero});
        case Relation::Neq: return makeSignSet({AtomSign::Neg, AtomSign::Pos});
        case Relation::Geq: return makeSignSet({AtomSign::Zero, AtomSign::Pos});
        case Relation::Gt:  return makeSignSet({AtomSign::Pos});
    }
    return 0;
}

inline SignSet signToAtomSignSet(Sign s) {
    switch (s) {
        case Sign::Neg:   return makeSignSet({AtomSign::Neg});
        case Sign::Zero:  return makeSignSet({AtomSign::Zero});
        case Sign::Pos:   return makeSignSet({AtomSign::Pos});
        case Sign::Unknown: return 0;
    }
    return 0;
}

// ------------------------------------------------------------------
// V3: Poly role and reasoned polynomial
// ------------------------------------------------------------------
enum class PolyRole : uint8_t {
    ConstraintPolynomial,
    ProjectionPolynomial,
    BoundaryPolynomial,
    DelineationPolynomial
};

struct ReasonedPolynomial {
    RationalPolynomial poly;
    PolyRole role = PolyRole::ConstraintPolynomial;
    std::vector<SatLit> reasons;
};

struct LocalProjectionResult {
    bool hasDegeneracy = false;
    std::vector<ReasonedPolynomial> polys;
    CdcacUnknownReason degeneracyReason = CdcacUnknownReason::None;
};

// ------------------------------------------------------------------
// V4: Projection input / context / fallback
// ------------------------------------------------------------------
struct ProjectionInput {
    std::vector<ReasonedPolynomial> polys;
    VarId eliminateVar;
    Cell baseCell;
};

struct ProjectionContext {
    int level = -1;
    VarId currentVar = NullVar;
    SamplePoint prefix;
    PolynomialKernel* kernel = nullptr;
    AlgebraBackend* algebra = nullptr;
};

// ------------------------------------------------------------------
// V3: Cell certificate kind
// ------------------------------------------------------------------
enum class CellCertificateKind : uint8_t {
    SignInvariantViolation,
    SectionViolation,
    FullLineViolation,
    LiftedCoveringInvariant,
    NullificationConflict,
    EquationalConstraintConflict
};

// ------------------------------------------------------------------
// V3: Atom condition
// ------------------------------------------------------------------
struct AtomCondition {
    AtomId atom = NullAtom;
    PolyId poly = NullPoly;
    Relation rel = Relation::Eq;
    SignSet allowedSigns = 0;
    SignSet invariantSigns = 0;
    bool isConstant = false;
};

// ------------------------------------------------------------------
// V3: Reason literal with polarity and normalized atom
// ------------------------------------------------------------------
struct CertificateReasonLit {
    SatLit lit{0, true};
    AtomId atom = NullAtom;
    bool polarity = true;
    NormalizedAtom normalized;
};

// ------------------------------------------------------------------
// V3: Projection obligation ID
// ------------------------------------------------------------------
struct ProjectionObligationId {
    uint64_t id = 0;
    bool operator==(const ProjectionObligationId& o) const { return id == o.id; }
    bool operator!=(const ProjectionObligationId& o) const { return id != o.id; }
};

// ------------------------------------------------------------------
// V3: Non-zero certificate
// ------------------------------------------------------------------
struct NonZeroCertificate {
    PolyId poly = NullPoly;
    Cell baseCell;
    AtomSign invariantSign = AtomSign::Pos;
    std::vector<ProjectionObligationId> obligations;
};

// ------------------------------------------------------------------
// V3: Projection obligation
// ------------------------------------------------------------------
enum class ObligationKind : uint8_t {
    NonVanishing,
    Delineable,
    DegreeInvariant,
    ProjectionCompleteness,
    ResultantSeparation,
    DiscriminantNonZero,
    LeadingCoefficientNonZero,
    ECValidity,
    NullificationRepairSoundness
};

enum class ProjectionPolicyKind : uint8_t {
    CollinsConservative,
    McCallumReduced,
    LazardStyle,
    ECReduced,
    HybridAdaptive
};

// ------------------------------------------------------------------
// V4: Fallback condition
// ------------------------------------------------------------------
struct FallbackCondition {
    enum class Kind { ObligationFailed, ECNotApplicable, ReducedNotValid } kind;
    ProjectionPolicyKind fallbackTo = ProjectionPolicyKind::CollinsConservative;
    std::vector<ProjectionObligationId> failedObligations;
    CdcacUnknownReason reason = CdcacUnknownReason::None;
};

struct ProjectionObligation {
    ProjectionObligationId id;
    PolyId targetPoly = NullPoly;
    VarId mainVar = NullVar;
    Cell baseCell;
    ObligationKind kind = ObligationKind::NonVanishing;
    ProjectionPolicyKind policy = ProjectionPolicyKind::CollinsConservative;
    std::vector<PolyId> witnessPolys;
    std::vector<NonZeroCertificate> witnesses;
};

// ------------------------------------------------------------------
// V4: Policy-level projection result
// ------------------------------------------------------------------
struct PolicyProjectionResult {
    ProjectionPolicyKind kind = ProjectionPolicyKind::CollinsConservative;
    std::vector<ReasonedPolynomial> projectionPolys;
    std::vector<ProjectionObligation> obligations;
    bool isReduced = false;
    std::optional<FallbackCondition> fallbackCondition;
    CdcacUnknownReason degeneracyReason = CdcacUnknownReason::None;
    bool hasDegeneracy = false;
};

// ------------------------------------------------------------------
// V4: Delineability condition
// ------------------------------------------------------------------
struct DelineabilityCondition {
    PolyId poly = NullPoly;
    VarId mainVar = NullVar;
    Cell baseCell;
    std::vector<NonZeroCertificate> leadingCoeffNonzero;
    std::vector<NonZeroCertificate> discriminantNonzero;
    std::vector<NonZeroCertificate> resultantNonzero;
    std::vector<ProjectionObligationId> obligations;
};

// ------------------------------------------------------------------
// V3: Sign invariant certificate
// ------------------------------------------------------------------
struct SignInvariantCertificate {
    PolyId poly = NullPoly;
    VarId mainVar = NullVar;
    Cell baseCell;
    Cell liftedCell;
    AtomSign invariantSign = AtomSign::Pos;
    std::vector<ProjectionObligationId> obligations;
};

// ------------------------------------------------------------------
// V3: Algebraic endpoint
// ------------------------------------------------------------------
enum class EndpointKind : uint8_t {
    MinusInfinity,
    PlusInfinity,
    Algebraic
};

struct AlgebraicEndpoint {
    EndpointKind kind = EndpointKind::Algebraic;
    std::optional<RealAlg> value;
};

// ------------------------------------------------------------------
// V3: Fiber cell coverage
// ------------------------------------------------------------------
enum class FiberCellKind : uint8_t {
    Sector,
    Section,
    MinusInfinitySector,
    PlusInfinitySector,
    FullLine
};

struct FiberCellCoverage {
    FiberCellKind kind = FiberCellKind::Sector;
    Cell cell;
    AlgebraicEndpoint lower;
    AlgebraicEndpoint upper;
    bool lowerOpen = true;
    bool upperOpen = true;
    std::optional<PolyId> sectionDefiningPoly;
    size_t certifiedCellIndex = 0;
};

// ------------------------------------------------------------------
// V3: Coverage certificate
// ------------------------------------------------------------------
struct CoverageCertificate {
    int level = -1;
    VarId var = NullVar;
    Cell parentCell;
    std::vector<FiberCellCoverage> orderedCells;
    bool coversWholeFiber = false;
};

// ------------------------------------------------------------------
// V3: Forward declaration for recursive type
// ------------------------------------------------------------------
struct CoveringCertificate;

// ------------------------------------------------------------------
// V3: Cell certificate — move-only, out-of-line destructor
// ------------------------------------------------------------------
struct CellCertificate {
    CellCertificateKind kind = CellCertificateKind::SignInvariantViolation;
    int level = -1;
    VarId var = NullVar;
    Cell cell;
    std::vector<AtomCondition> atomConditions;
    std::vector<SignInvariantCertificate> signCerts;
    std::vector<CertificateReasonLit> reasons;
    std::vector<PolyId> guards;
    std::unique_ptr<CoveringCertificate> childCoverCert;

    CellCertificate();
    ~CellCertificate();
    CellCertificate(CellCertificate&&) noexcept;
    CellCertificate& operator=(CellCertificate&&) noexcept;
    CellCertificate(const CellCertificate&) = delete;
    CellCertificate& operator=(const CellCertificate&) = delete;
};

// ------------------------------------------------------------------
// V3: Certified cell — cell + its certificate
// ------------------------------------------------------------------
struct CertifiedCell {
    Cell cell;
    CellCertificate certificate;
};

// ------------------------------------------------------------------
// V4: Nullification repair
// ------------------------------------------------------------------
enum class NullificationRepairKind : uint8_t {
    NoRepairNeeded,
    ConstraintDropped,
    ImmediateConflict,
    ReplacementPolys,
    Unknown
};

struct NullificationRepair {
    NullificationRepairKind kind = NullificationRepairKind::Unknown;
    std::vector<ReasonedPolynomial> replacementPolys;
    std::vector<ProjectionObligation> newObligations;
    std::optional<CertifiedCell> immediateConflict;
    CdcacUnknownReason reason = CdcacUnknownReason::None;
};

// ------------------------------------------------------------------
// V3: Covering certificate
// ------------------------------------------------------------------
struct CoveringCertificate {
    int level = -1;
    VarId var = NullVar;
    Cell parentCell;
    std::vector<CertifiedCell> cells;
    std::vector<ReasonedPolynomial> projectionBasis;
    std::vector<ProjectionObligation> projectionObligations;
    CoverageCertificate coverage;
};

} // namespace zolver
