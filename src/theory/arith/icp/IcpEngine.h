#pragma once

#include "theory/arith/icp/Contractor.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/arith/icp/IcpResult.h"
#include "theory/arith/icp/Worklist.h"
#include "theory/arith/interval/ReasonedBox.h"
#include <memory>
#include <vector>

namespace xolver {

class IcpEngine {
public:
    IcpResultZ run(
        const std::vector<std::unique_ptr<Contractor>>& contractors,
        const WatcherMap& watchers,
        ReasonedBox& box,
        const IcpConfig& config);
};

} // namespace xolver
