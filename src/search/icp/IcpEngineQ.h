#pragma once

#include "search/icp/Contractor.h"
#include "search/icp/IcpTypes.h"
#include "search/icp/IcpResult.h"
#include "search/icp/Worklist.h"
#include "algebra/interval/ReasonedBoxQ.h"
#include <memory>
#include <vector>

namespace xolver {

// Rational ICP contractors narrow the box directly. NoChange reports a
// completed worklist; callers read accumulated bounds and reasons from box,
// including when a work budget expires before the fixpoint. Conflicts retain
// the responsible constraint/domain reasons, including already-empty inputs.
class IcpEngineQ {
public:
    IcpResultQ run(
        const std::vector<std::unique_ptr<ContractorQ>>& contractors,
        const WatcherMap& watchers,
        ReasonedBoxQ& box,
        const IcpConfig& config);
};

} // namespace xolver
