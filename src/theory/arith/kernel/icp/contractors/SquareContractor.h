#pragma once

#include "theory/arith/kernel/icp/Contractor.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include <memory>

namespace xolver {

/**
 * SquareContractor: recognizes x^2 - c rel 0 pattern for NIA.
 *
 * V1: only interval updates, no finite-set refinement.
 */
class SquareContractor : public Contractor {
public:
    SquareContractor(const IcpConstraint& constraint, PolynomialKernel& kernel);

    ContractorResultZ contract(ReasonedBox& box) override;
    std::vector<std::string> vars() const override;
    SatLit reason() const override;

private:
    IcpConstraint constraint_;
    PolynomialKernel& kernel_;
    std::vector<std::string> vars_;

    // Check if poly matches a*x^2 + b where a = ±1, b = ∓c
    // Returns the sign (1 for x^2-c, -1 for -x^2+c) and constant c
    bool recognizePattern(int& sign, mpz_class& c) const;
};

} // namespace xolver
