#pragma once

#include "theory/arith/icp/Contractor.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <gmpxx.h>
#include <string>
#include <vector>

namespace xolver {

// V5c — pure bilinear / linear-in-live with interval coefficient.
//
// Targets polynomials of the shape:
//     B(rest) · liveVar  +  C(rest)   rel  0
// with NO term of degree ≥ 2 in liveVar (otherwise V4/V5b cover it).
//
// At least one bTerm is required (otherwise the polynomial is constant
// in liveVar — nothing to narrow). bTerms may be pure live^1 (just the
// var) or mixed (live · rest factors); both produce an interval-valued
// linear coefficient B over the rest box. cTerms are live-free.
//
// Math: B·x + C ≤ 0 ⇔ x ≤ -C/B (when B > 0); flip when B < 0. With B
// and C interval-valued, x ≤ max(-C/B) over the rest box. We compute
// -C/B = D · (1/B) where D = -C, via interval multiplication after
// inverting B. Inversion is well-defined only when B is sign-pinned
// (Bl > 0 or Bh < 0); when 0 ∈ B's box we decline because 1/B explodes.
//
// Eq: B·x + C = 0 ⇔ x = -C/B ⇒ bracket [-C/B].lo, [-C/B].hi.
//
// Closes the "Mixed terms (x·y)" coverage gap — e.g. x·y - 1 = 0 with
// y sign-pinned narrows x to the hyperbolic feasible region.
class BilinearContractorQ : public ContractorQ {
public:
    BilinearContractorQ(
        const IcpConstraint& constraint,
        PolynomialKernel& kernel,
        const std::string& liveVar);

    bool isUsable() const { return usable_; }

    ContractorResultQ contract(ReasonedBoxQ& box) override;
    std::vector<std::string> vars() const override;
    SatLit reason() const override;

private:
    IcpConstraint constraint_;
    PolynomialKernel& kernel_;
    std::string liveVar_;
    std::vector<std::string> allVars_;

    bool usable_ = false;
    std::vector<PolynomialKernel::MonomialTerm> bTerms_;
    std::vector<PolynomialKernel::MonomialTerm> cTerms_;

    std::optional<IntervalQ> evalTerms(
        const std::vector<PolynomialKernel::MonomialTerm>& terms,
        const ReasonedBoxQ& box,
        std::vector<SatLit>& usedReasons,
        VarId liveVarId) const;
};

} // namespace xolver
