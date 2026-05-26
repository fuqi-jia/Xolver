#pragma once

#include "theory/arith/interval/ReasonedBoxZ.h"
#include "theory/arith/interval/ReasonedBoxQ.h"
#include "theory/arith/icp/IcpResult.h"
#include <string>
#include <vector>

namespace zolver {

class ContractorZ {
public:
    virtual ~ContractorZ() = default;
    virtual ContractorResultZ contract(ReasonedBoxZ& box) = 0;
    virtual std::vector<std::string> vars() const = 0;
    virtual SatLit reason() const = 0;
};

class ContractorQ {
public:
    virtual ~ContractorQ() = default;
    virtual ContractorResultQ contract(ReasonedBoxQ& box) = 0;
    virtual std::vector<std::string> vars() const = 0;
    virtual SatLit reason() const = 0;
};

} // namespace zolver
