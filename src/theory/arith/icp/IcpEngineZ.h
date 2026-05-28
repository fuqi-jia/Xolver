#pragma once

#include "theory/arith/icp/Contractor.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/arith/icp/IcpResult.h"
#include "theory/arith/icp/Worklist.h"
#include "theory/arith/interval/ReasonedBoxZ.h"
#include <memory>
#include <vector>

namespace xolver {

class IcpEngineZ {
public:
    IcpResultZ run(
        const std::vector<std::unique_ptr<ContractorZ>>& contractors,
        const WatcherMap& watchers,
        ReasonedBoxZ& box,
        const IcpConfig& config);
};

} // namespace xolver
