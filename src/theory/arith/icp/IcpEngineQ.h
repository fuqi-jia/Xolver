#pragma once

#include "theory/arith/icp/Contractor.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/arith/icp/IcpResult.h"
#include "theory/arith/icp/Worklist.h"
#include "theory/arith/interval/ReasonedBoxQ.h"
#include <memory>
#include <vector>

namespace xolver {

// Rational-side ICP engine — symmetric mirror of IcpEngine for NRA.
// Sound by construction: only emits Conflict when a contractor reports a
// definitively-violated constraint, with reasons that combine the constraint
// reason with the interval reasons that produced the violating box.
class IcpEngineQ {
public:
    IcpResultQ run(
        const std::vector<std::unique_ptr<ContractorQ>>& contractors,
        const WatcherMap& watchers,
        ReasonedBoxQ& box,
        const IcpConfig& config);
};

} // namespace xolver
