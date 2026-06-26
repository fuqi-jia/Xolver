#pragma once

#include "theory/arith/kernel/interval/ReasonedBox.h"
#include "theory/arith/kernel/interval/ReasonedBoxQ.h"
#include "theory/arith/kernel/icp/IcpResult.h"
#include <string>
#include <vector>

namespace xolver {

class Contractor {
public:
    virtual ~Contractor() = default;
    virtual ContractorResultZ contract(ReasonedBox& box) = 0;
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

} // namespace xolver
