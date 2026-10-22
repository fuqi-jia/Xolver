#pragma once

#include "search/icp/Contractor.h"
#include "search/icp/IcpTypes.h"
#include "search/icp/IcpResult.h"
#include "search/icp/Worklist.h"
#include "algebra/interval/ReasonedBox.h"
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
