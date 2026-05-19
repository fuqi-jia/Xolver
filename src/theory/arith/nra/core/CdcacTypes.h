#pragma once
#include "theory/arith/nra/core/CdcacCommon.h"
struct AlgebraicRoot {
    UniPolyId definingPoly = NullUniPolyId;  // univariate after specialization
    int rootIndex = -1;                       // ordered real root index (0-based)
    mpq_class lower;                          // isolating interval [lower, upper]
    mpq_class upper;
    std::vector<RootOrigin> origins;          // provenance (may have multiple sources)
};

struct RealAlg {
    enum class Kind { Rational, AlgebraicRoot };
    Kind kind = Kind::Rational;
    mpq_class rational;       // valid if kind == Rational
    AlgebraicRoot root;       // valid if kind == AlgebraicRoot

    // Factory methods
    static RealAlg fromRational(mpq_class q) {
        RealAlg r;
        r.kind = Kind::Rational;
        r.rational = std::move(q);
        return r;
    }
    static RealAlg fromAlgebraic(AlgebraicRoot ar) {
        RealAlg r;
        r.kind = Kind::AlgebraicRoot;
        r.root = std::move(ar);
        return r;
    }

    bool isRational() const { return kind == Kind::Rational; }
    bool isAlgebraic() const { return kind == Kind::AlgebraicRoot; }
};

// ------------------------------------------------------------------
// Sample point: partial or full assignment to variables
// ------------------------------------------------------------------
struct SamplePoint {
    std::vector<VarId> varOrder;
    std::vector<RealAlg> values;  // parallel to varOrder

    size_t numVars() const { return varOrder.size(); }
    bool empty() const { return varOrder.empty(); }

    void push(VarId v, RealAlg val) {
        varOrder.push_back(v);
        values.push_back(std::move(val));
    }
    void pop() {
        if (!varOrder.empty()) {
            varOrder.pop_back();
            values.pop_back();
        }
    }
    void clear() {
        varOrder.clear();
        values.clear();
    }
};

// ------------------------------------------------------------------
// Root set from univariate root isolation
// ------------------------------------------------------------------
struct RootSet {
    std::vector<RealAlg> roots;  // sorted by value
    int numRoots() const { return static_cast<int>(roots.size()); }
    bool empty() const { return roots.empty(); }
};

// ------------------------------------------------------------------
// Cell kinds
// ------------------------------------------------------------------
enum class CellKind : uint8_t {
    FullLine,   // (-inf, +inf)
    Sector,     // open interval between roots
    Section     // exactly one root
};

// ------------------------------------------------------------------
// Bound on a cell
// ------------------------------------------------------------------
struct Bound {
    enum class Kind { NegInf, PosInf, Rational, AlgebraicRoot } kind;
    RealAlg value;   // valid if kind == Rational or AlgebraicRoot
    bool open = true;

    // Factory methods
    static Bound negInf() {
        return {Kind::NegInf, RealAlg::fromRational(0), true};
    }
    static Bound posInf() {
        return {Kind::PosInf, RealAlg::fromRational(0), true};
    }
    static Bound rational(mpq_class q, bool isOpen) {
        return {Kind::Rational, RealAlg::fromRational(std::move(q)), isOpen};
    }
    static Bound algebraic(AlgebraicRoot ar, bool isOpen) {
        return {Kind::AlgebraicRoot, RealAlg::fromAlgebraic(std::move(ar)), isOpen};
    }

    bool isNegInf() const { return kind == Kind::NegInf; }
    bool isPosInf() const { return kind == Kind::PosInf; }
    bool isRational() const { return kind == Kind::Rational; }
    bool isAlgebraic() const { return kind == Kind::AlgebraicRoot; }
};

// Forward declaration
struct Covering;

// ------------------------------------------------------------------
// Section data: extra information for section cells
// ------------------------------------------------------------------
struct SectionData {
    PolyId liftedDefiningPoly = NullPoly;      // original multivariate polynomial
    UniPolyId squarefreeDefiningPoly = NullUniPolyId;  // univariate squarefree polynomial
    RootOrigin origin;
};

// ------------------------------------------------------------------
// Extended real algebraic number (includes ±inf)
// ------------------------------------------------------------------
struct ExtRealAlg {
    bool isNegInf = false;
    bool isPosInf = false;
    RealAlg value;  // valid if !isNegInf && !isPosInf

    static ExtRealAlg negInfinity() {
        ExtRealAlg e;
        e.isNegInf = true;
        return e;
    }
    static ExtRealAlg posInfinity() {
        ExtRealAlg e;
        e.isPosInf = true;
        return e;
    }
    static ExtRealAlg fromRealAlg(RealAlg r) {
        ExtRealAlg e;
        e.value = std::move(r);
        return e;
    }
};

// ------------------------------------------------------------------
// Well-formed check result (three-state)
// ------------------------------------------------------------------
enum class WellFormedKind : uint8_t {
    Valid,
    Invalid,
    Unknown
};

struct WellFormedResult {
    WellFormedKind kind = WellFormedKind::Unknown;
    CdcacUnknownReason reason = CdcacUnknownReason::None;
};

// ------------------------------------------------------------------
// Cell contains sample result (three-state)
// ------------------------------------------------------------------
enum class ContainsResult : uint8_t {
    True,
    False,
    Unknown
};

// ------------------------------------------------------------------
// Pick sample result (three-state)
// ------------------------------------------------------------------
enum class PickKind {
    Sample,
    Covered,
    Unknown
};

struct PickSampleResult {
    PickKind kind = PickKind::Unknown;
    RealAlg sample;
    CdcacUnknownReason reason = CdcacUnknownReason::None;
};

// ------------------------------------------------------------------
// Cell: a region of the real line for one variable
// ------------------------------------------------------------------
struct Cell {
    VarId var = NullVar;
    CellKind kind = CellKind::Sector;
    Bound lower = Bound::negInf();
    Bound upper = Bound::posInf();

    // Active true literals supporting this cell's local refutation.
    // Conflict clause = OR(not reason_i) for all reasons in the covering.
    std::vector<SatLit> reasons;

    // Projection polynomials guaranteeing sign-invariance / delineability
    std::vector<PolyId> guards;

    bool isSection() const { return kind == CellKind::Section; }
    bool isSector() const { return kind == CellKind::Sector; }

    // V2-6: section metadata (populated for Section cells)
    std::optional<SectionData> section;
};

// ------------------------------------------------------------------
// Covering: a set of cells whose union covers the real line
// ------------------------------------------------------------------
struct Covering {
    VarId var = NullVar;
    std::vector<Cell> cells;

    bool empty() const { return cells.empty(); }
    // coversAllLine() is implemented in CoveringManager with an AlgebraBackend comparator.

    // Pick a sample outside all cells. If preferred is given and not covered, use it.
    PickSampleResult chooseSampleOutside(const std::optional<mpq_class>& preferred) const;
};

// ------------------------------------------------------------------
// Cell lookup result (three-value, propagates uncertainty)
// ------------------------------------------------------------------
enum class CellLookupStatus : uint8_t {
    Found,
    Unknown,       // compareRealAlg returned Unknown
    InvalidInput   // root set not sorted (duplicate or inverted)
};

struct CellLookupResult {
    CellLookupStatus status = CellLookupStatus::InvalidInput;
    Cell cell;
};

// ------------------------------------------------------------------
// Build conflict cell result (P2b shallow generalization)
// ------------------------------------------------------------------
enum class BuildCellStatus : uint8_t {
    Success,
    Unknown
};

// ------------------------------------------------------------------
// V3: Normalized atom representation for certificates
// ------------------------------------------------------------------
struct NormalizedAtom {
    PolyId poly = NullPoly;
    Relation rel = Relation::Eq;
};

// ------------------------------------------------------------------
// V3: Bitflag sign for certificate invariant sets
// (Existing Sign enum {-1,0,1,2} is kept for runtime evaluation.)
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
// ------------------------------------------------------------------
// V3: Poly role and reasoned polynomial (moved from LocalProjection.h)
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
    Cell baseCell;  // obligation scope
};

struct ProjectionContext {
    int level = -1;
    VarId currentVar = NullVar;
    SamplePoint prefix;
    PolynomialKernel* kernel = nullptr;
    AlgebraBackend* algebra = nullptr;
};

// Note: FallbackCondition is defined after ProjectionPolicyKind.
// PolicyProjectionResult, DelineabilityCondition, NullificationRepair
// are defined later (after ProjectionObligation / CertifiedCell) to avoid
// incomplete-type issues.

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
// V3: Atom condition — every conflict cell has non-empty atomConditions
// ------------------------------------------------------------------
struct AtomCondition {
    AtomId atom = NullAtom;
    PolyId poly = NullPoly;
    Relation rel = Relation::Eq;
    SignSet allowedSigns = 0;      // signSetFromRelation(rel)
    SignSet invariantSigns = 0;    // exact sign(s) poly takes on the ENTIRE cell
    bool isConstant = false;       // true if poly is a constant
};

// ------------------------------------------------------------------
// V3: Reason literal with polarity and normalized atom
// ------------------------------------------------------------------
struct CertificateReasonLit {
    SatLit lit{0, true};
    AtomId atom = NullAtom;
    bool polarity = true;          // true = atom as asserted, false = negated
    NormalizedAtom normalized;     // {poly, relation}
};

// ------------------------------------------------------------------
// V3: Projection obligation ID (forward-referenced by certificates)
// ------------------------------------------------------------------
struct ProjectionObligationId {
    uint64_t id = 0;
    bool operator==(const ProjectionObligationId& o) const { return id == o.id; }
    bool operator!=(const ProjectionObligationId& o) const { return id != o.id; }
};

// ------------------------------------------------------------------
// V3: Non-zero certificate (witness that a poly is non-zero on a cell)
// ------------------------------------------------------------------
struct NonZeroCertificate {
    PolyId poly = NullPoly;
    Cell baseCell;
    AtomSign invariantSign = AtomSign::Pos;  // Pos or Neg, never Zero
    std::vector<ProjectionObligationId> obligations;
};

// ------------------------------------------------------------------
// V3: Projection obligation — scoped to a baseCell, not global
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
// V4: Fallback condition — placed after ProjectionPolicyKind
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
    Cell baseCell;                           // scoped to THIS base cell
    ObligationKind kind = ObligationKind::NonVanishing;
    ProjectionPolicyKind policy = ProjectionPolicyKind::CollinsConservative;
    std::vector<PolyId> witnessPolys;
    std::vector<NonZeroCertificate> witnesses;
};

// ------------------------------------------------------------------
// V4: Policy-level projection result (wraps LocalProjectionResult)
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
// V4: Delineability condition — witness-bearing
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
// V3: Sign invariant certificate — proves sign invariance via obligations
// ------------------------------------------------------------------
struct SignInvariantCertificate {
    PolyId poly = NullPoly;
    VarId mainVar = NullVar;
    Cell baseCell;         // parent cell this lifts over
    Cell liftedCell;       // the cell itself
    AtomSign invariantSign = AtomSign::Pos;
    std::vector<ProjectionObligationId> obligations;
};

// ------------------------------------------------------------------
// V3: Algebraic endpoint — pure value, no open/closed flag
// ------------------------------------------------------------------
enum class EndpointKind : uint8_t {
    MinusInfinity,
    PlusInfinity,
    Algebraic
};

struct AlgebraicEndpoint {
    EndpointKind kind = EndpointKind::Algebraic;
    std::optional<RealAlg> value;  // present iff kind == Algebraic
};

// ------------------------------------------------------------------
// V3: Fiber cell coverage — one-to-one with CertifiedCell
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
    std::optional<PolyId> sectionDefiningPoly;  // non-null iff kind == Section
    size_t certifiedCellIndex = 0;
};

// ------------------------------------------------------------------
// V3: Coverage certificate — ordered cells, seamless parent fiber coverage
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
// V4: Nullification repair — produces verifiable obligations
// ------------------------------------------------------------------
enum class NullificationRepairKind : uint8_t {
    NoRepairNeeded,
    ConstraintDropped,       // 0 = 0, constraint vanishes and is tautologically true
    ImmediateConflict,       // nullification leads to immediate certified conflict
    ReplacementPolys,        // replace with substitute polynomials + obligations
    Unknown                  // cannot repair
};

struct NullificationRepair {
    NullificationRepairKind kind = NullificationRepairKind::Unknown;
    std::vector<ReasonedPolynomial> replacementPolys;
    std::vector<ProjectionObligation> newObligations;
    std::optional<CertifiedCell> immediateConflict;  // certified, not raw Cell
    CdcacUnknownReason reason = CdcacUnknownReason::None;
};

// ------------------------------------------------------------------
// V3: Covering certificate — full covering with per-cell certificates
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
    std::optional<CertifiedCell> conflictCell;  // ONLY for Unsat
    std::optional<SamplePoint> satSample;       // ONLY for Sat
    CdcacUnknownReason unknownReason = CdcacUnknownReason::None;  // ONLY for Unknown
};

// ------------------------------------------------------------------
// CDCAC result with optional unsat certificate and covering certificate
// Defined after CoveringCertificate so std::optional<CoveringCertificate> works.
// ------------------------------------------------------------------
struct CdcacUnsatCertificate {
    Covering covering;
    std::vector<SatLit> reasons;
};

struct CdcacResult {
    CdcacStatus status = CdcacStatus::Unknown;
    std::optional<SamplePoint> model;
    std::optional<CdcacUnsatCertificate> unsat;
    std::optional<CoveringCertificate> coveringCert;  // V3: optional covering certificate
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

} // namespace nlcolver
