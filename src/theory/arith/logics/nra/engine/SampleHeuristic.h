#pragma once

#include "theory/arith/logics/nra/core/CdcacTypes.h"
#include <optional>

namespace xolver {

class AlgebraBackend;

// ------------------------------------------------------------------
// V6: Sample selection heuristic
// ------------------------------------------------------------------
enum class SampleStrategy : uint8_t {
    ZeroFirst,           // try 0 first
    RationalSmallFirst,  // smallest |q| first
    BoundarySectionFirst,// sample on section boundaries
    SectorMidpointFirst, // midpoint of sector
    ConflictAvoiding,    // avoid previously conflicted samples
    ModelGuided          // use LRA/linearizer seed
};

struct SampleHeuristicResult {
    RealAlg sample;
    bool success = false;
};

class SampleHeuristic {
public:
    explicit SampleHeuristic(AlgebraBackend* algebra);

    SampleHeuristicResult pick(
        VarId var,
        const Cell& cell,
        const std::optional<mpq_class>& seed,
        SampleStrategy strategy = SampleStrategy::ZeroFirst);

    // Pick a sample for a sector cell
    SampleHeuristicResult pickSector(
        VarId var,
        const Bound& lower,
        const Bound& upper,
        const std::optional<mpq_class>& seed);

    // Pick a sample for a section cell
    SampleHeuristicResult pickSection(
        VarId var,
        const RealAlg& root);

private:
    AlgebraBackend* algebra_;
};

} // namespace xolver
