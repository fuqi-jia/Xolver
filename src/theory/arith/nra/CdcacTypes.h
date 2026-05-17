#pragma once

#include "expr/types.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>
#include <cstdint>
#include <vector>
#include <optional>
#include <string>
#include <variant>
#include <unordered_map>
#include <cassert>

namespace nlcolver {

// ------------------------------------------------------------------
// IDs
// ------------------------------------------------------------------
using ConstraintId = uint32_t;
using UniPolyId    = uint32_t;

constexpr ConstraintId NullConstraintId = std::numeric_limits<ConstraintId>::max();
constexpr UniPolyId    NullUniPolyId    = std::numeric_limits<UniPolyId>::max();

// ------------------------------------------------------------------
// Unknown reason (for debugging and stats)
// ------------------------------------------------------------------
enum class CdcacUnknownReason {
    None,

    // Algebraic / evaluation
    BackendFailure,
    RootIsolationInvalid,
    RootIsolationFailed,
    SignEvaluationInconclusive,
    UnsupportedAlgebraicSection,
    AlgebraicComparisonInconclusive,
    MissingDefiningPoly,

    // Polynomial arithmetic
    ExactDivisionFailed,
    SquarefreeFailed,
    GcdFailed,
    SubresultantFailed,
    ParametricDegreeDrop,
    PseudoRemainderFailed,
    LeadingCoefficientNullified,

    // Projection / generalization
    ProjectionDegeneracyUnresolved,
    SpecializationFailed,
    NullificationInGeneralization,
    NullificationUnresolved,
    CellConstructionFailed,
    GeneralizedCellDoesNotContainSample,
    MalformedCell,
    CoveringDidNotGrow,

    // Reason / proof
    ReasonReplayFailed,
    ReasonMinimizationFailed,

    // Resource / internal
    ResourceBudgetExceeded,
    InternalInvariantViolation
};

// ------------------------------------------------------------------
// Effort levels
// ------------------------------------------------------------------
enum class CdcacEffort : uint8_t {
    Cheap,      // constants, duplicates, simple bounds
    Standard,   // + incremental linearization, LRA model, cuts
    Full        // + CDCAC complete check
};

// ------------------------------------------------------------------
// Core CDCAC result kinds
// ------------------------------------------------------------------
enum class CdcacStatus : uint8_t {
    Sat,
    Unsat,
    Unknown
};

// ------------------------------------------------------------------
// Sign of a polynomial evaluation
// ------------------------------------------------------------------
enum class Sign : int8_t {
    Neg = -1,
    Zero = 0,
    Pos = 1,
    Unknown = 2
};

inline Sign multiplySigns(Sign a, Sign b) {
    if (a == Sign::Unknown || b == Sign::Unknown) return Sign::Unknown;
    if (a == Sign::Zero || b == Sign::Zero) return Sign::Zero;
    int prod = static_cast<int>(a) * static_cast<int>(b);
    return (prod > 0) ? Sign::Pos : Sign::Neg;
}

// ------------------------------------------------------------------
// Real algebraic number comparison result
// ------------------------------------------------------------------
enum class CompareResult : int8_t {
    Less = -1,
    Equal = 0,
    Greater = 1,
    Unknown = 2
};

// ------------------------------------------------------------------
// Root membership in another polynomial
// ------------------------------------------------------------------
enum class RootLocateStatus : uint8_t {
    Belongs,
    NotBelongs,
    Unknown
};

struct RootLocateResult {
    RootLocateStatus status = RootLocateStatus::Unknown;
    int rootIndexInTarget = -1;
};

// ------------------------------------------------------------------
// Coverage check result for cell decomposition
// ------------------------------------------------------------------
enum class CoverageResult : uint8_t {
    Covers,
    DoesNotCover,
    Unknown
};

// ------------------------------------------------------------------
// Tower reduction result (P3)
// ------------------------------------------------------------------
struct ReductionResult {
    enum class Status : uint8_t { Zero, NonZero, Unknown } status;
    PolyId poly = NullPoly;   // valid if NonZero

    static ReductionResult zero() { return {Status::Zero, NullPoly}; }
    static ReductionResult nonzero(PolyId p) { return {Status::NonZero, p}; }
    static ReductionResult unknown() { return {Status::Unknown, NullPoly}; }

    bool isZero() const { return status == Status::Zero; }
    bool isNonZero() const { return status == Status::NonZero; }
    bool isUnknown() const { return status == Status::Unknown; }
};

// ------------------------------------------------------------------
// Projection mode
// ------------------------------------------------------------------
enum class ProjectionMode : uint8_t {
    McCallum,
    Lazard,
    Conservative
};

// ------------------------------------------------------------------
// Projection result status
// ------------------------------------------------------------------
enum class ProjectionStatus : uint8_t {
    Success,
    UnsupportedVarOrder,    // libpoly main_variable != eliminateVar
    UnsupportedMode,        // only Conservative is supported in P2b
    BackendFailure,         // exception during discriminant/resultant/coeff
    EmptyBecauseNoRelevantPolys
};

struct ProjectionResult {
    ProjectionStatus status = ProjectionStatus::BackendFailure;
    std::vector<PolyId> polys;
};

// ------------------------------------------------------------------
// Vanish result (for nullification detection)
// ------------------------------------------------------------------
enum class VanishResult : uint8_t {
    Vanishes,
    NonVanishes,
    Unknown
};

// ------------------------------------------------------------------
// Model seed from LRA / linearizer
// ------------------------------------------------------------------
struct ModelSeed {
    std::unordered_map<VarId, mpq_class> values;
};

// ------------------------------------------------------------------
// Provenance: where an algebraic root came from
// ------------------------------------------------------------------
using PrefixContextId = uint32_t;

struct RootOrigin {
    PolyId liftedDefiningPoly = NullPoly;      // original multivariate polynomial
    UniPolyId squarefreeDefiningPoly = NullUniPolyId;  // tower reduction divisor
    VarId mainVar = NullVar;                    // variable this root belongs to
    int level = -1;                             // index in varOrder
    int rootIndex = -1;                         // which root of the defining polynomial
    PrefixContextId contextId = 0;              // sample prefix where this root was created
};

// ------------------------------------------------------------------
// Real algebraic number: rational or algebraic root
// ------------------------------------------------------------------
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
// CDCAC result with optional unsat certificate (including covering)
// ------------------------------------------------------------------
struct CdcacUnsatCertificate {
    Covering covering;
    std::vector<SatLit> reasons;
};

struct CdcacResult {
    CdcacStatus status = CdcacStatus::Unknown;
    std::optional<SamplePoint> model;
    std::optional<CdcacUnsatCertificate> unsat;
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

struct BuildCellResult {
    BuildCellStatus status = BuildCellStatus::Unknown;
    Cell cell;
};

} // namespace nlcolver
