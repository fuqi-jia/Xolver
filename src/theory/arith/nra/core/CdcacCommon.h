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
#include <memory>
#include <cassert>

// V3: ReasonedPolynomial depends on RationalPolynomial
#include "theory/arith/poly/RationalPolynomial.h"

namespace xolver {

// Forward declarations (used by V4 types)
class AlgebraBackend;

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
    AlgebraicIsolationCrash,

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
    // The projection closure underpinning this level's covering is not
    // complete (degeneracy / budget / an uncertified algebraic specialization),
    // so a UNSAT covering would over-generalize. Reported instead of unsound
    // UNSAT.
    ProjectionClosureIncomplete,

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

} // namespace xolver
