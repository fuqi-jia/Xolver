#pragma once

#include "theory/arith/interval/IntervalTypes.h"
#include "theory/arith/interval/IntervalQ.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/core/TheorySolver.h"
#include <optional>
#include <vector>

namespace xolver {

enum class IcpStatus {
    Conflict,
    DomainUpdate,
    SplitSuggestion,
    NoChange,
    UnknownBudget
};

struct BoundUpdateZ {
    std::string var;
    IntervalZ newInterval;
    std::vector<SatLit> reasons; // must include constraint reason + used bound reasons
};

struct BoundUpdateQ {
    std::string var;
    IntervalQ newInterval;
    std::vector<SatLit> reasons;
};

struct ContractorResultZ {
    IcpStatus status;
    std::optional<TheoryConflict> conflict;
    std::vector<BoundUpdateZ> updates;
};

struct ContractorResultQ {
    IcpStatus status;
    std::optional<TheoryConflict> conflict;
    std::vector<BoundUpdateQ> updates;
};

struct IcpResultZ {
    IcpStatus status;
    std::optional<TheoryConflict> conflict;
    std::vector<BoundUpdateZ> updates;
    std::optional<SplitSuggestion> split;
};

struct IcpResultQ {
    IcpStatus status;
    std::optional<TheoryConflict> conflict;
    std::vector<BoundUpdateQ> updates;
    std::optional<SplitSuggestion> split;
};

} // namespace xolver
