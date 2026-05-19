#pragma once
#include "theory/arith/nra/core/CdcacValue.h"

namespace nlcolver {

// ------------------------------------------------------------------
// Cell kinds
// ------------------------------------------------------------------
enum class CellKind : uint8_t {
    FullLine,   // (-inf, +inf)
    Sector,     // open interval between roots
    Section     // exactly one root
};

// ------------------------------------------------------------------
// Section data: extra information for section cells
// ------------------------------------------------------------------
struct SectionData {
    PolyId liftedDefiningPoly = NullPoly;
    UniPolyId squarefreeDefiningPoly = NullUniPolyId;
    RootOrigin origin;
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

    std::vector<SatLit> reasons;
    std::vector<PolyId> guards;

    bool isSection() const { return kind == CellKind::Section; }
    bool isSector() const { return kind == CellKind::Sector; }

    std::optional<SectionData> section;
};

// ------------------------------------------------------------------
// Covering: a set of cells whose union covers the real line
// ------------------------------------------------------------------
struct Covering {
    VarId var = NullVar;
    std::vector<Cell> cells;

    bool empty() const { return cells.empty(); }

    PickSampleResult chooseSampleOutside(const std::optional<mpq_class>& preferred) const;
};

// ------------------------------------------------------------------
// Cell lookup result (three-value, propagates uncertainty)
// ------------------------------------------------------------------
enum class CellLookupStatus : uint8_t {
    Found,
    Unknown,
    InvalidInput
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

} // namespace nlcolver
