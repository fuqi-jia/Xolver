#pragma once

#include "algebra/interval/IntervalTypes.h"
#include "algebra/interval/IntervalQ.h"
#include "search/icp/IcpTypes.h"
#include "contracts/TheorySolver.h"
#include <optional>
#include <string>
#include <vector>

namespace xolver {

enum class IcpStatus {
    Conflict,
    DomainUpdate,
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
};

struct IcpResultQ {
    IcpStatus status;
    std::optional<TheoryConflict> conflict;
    std::vector<BoundUpdateQ> updates;
};

} // namespace xolver
