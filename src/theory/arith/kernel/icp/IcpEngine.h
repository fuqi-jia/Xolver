#pragma once

#include "theory/arith/kernel/icp/Contractor.h"
#include "theory/arith/kernel/icp/IcpTypes.h"
#include "theory/arith/kernel/icp/IcpResult.h"
#include "theory/arith/kernel/icp/Worklist.h"
#include "theory/arith/kernel/interval/ReasonedBox.h"
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
