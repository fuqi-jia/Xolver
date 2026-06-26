#pragma once

#include "theory/arith/kernel/icp/Contractor.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include <gmpxx.h>
#include <string>
#include <vector>

namespace xolver {

// V5b — multivariate quadratic with mixed live^1 (also subsumes the
// bilinear x·y shape when it contributes to the live-linear coefficient).
//
// Targets polynomials of the shape:
//     a · liveVar^2  +  B(rest) · liveVar  +  C(rest)   rel  0
// where
//   - a is a scalar integer coefficient (the sum of all pure liveVar^2
//     terms; the live^2 monomial must NOT mix with another variable —
//     V5b doesn't yet handle terms like x²·y),
//   - B(rest) is a polynomial in non-live vars (from monomials that
//     contain liveVar with exponent 1, possibly multiplied by other
//     vars — i.e. live^1 alone is fine, live·y, live·y·z, etc.),
//   - C(rest) is a polynomial in non-live vars (live-free monomials).
//
// At least one live^1 term must be present; otherwise V4 covers this
// shape cleanly and V5b declines to avoid duplicate contractors. At
// least one live^2 term is required to make this a genuine quadratic.
//
// Soundness (Leq, a > 0): for some (B, C) in their box rectangle, the
// constraint a·x² + B·x + C ≤ 0 holds iff disc(B, C) = B² − 4aC ≥ 0
// and x ∈ [r1(B,C), r2(B,C)] = [(-B ± √disc)/(2a)]. The union over
// (B, C) box of these intervals is sound-over-approximated by
// [min(r1), max(r2)] using:
//     min r1 = (-max(B) − √(max disc)) / (2a)     [outward floor]
//     max r2 = (-min(B) + √(max disc)) / (2a)     [outward ceil]
// where max disc = max(B²) − 4a·min(C), treating B and C as independent.
// The "B and C independent" relaxation is a standard interval-arithmetic
// over-approximation — sound but slightly loose when B and C are
// correlated through shared rest variables. max(B²) accounts for B
// straddling zero (then min B² = 0, max stays at max(Bl², Bh²)).
//
// Eq is bidirectional: solutions are {r1, r2}, bracket [r1, r2] covers
// both. Same conflict rule (max disc < 0 ⇒ no solutions anywhere).
//
// Sign normalization: a < 0 with Leq/Lt is a union (parabola opens
// down); skip. a < 0 with Eq normalizes by negating (a, B, C) to a > 0.
// a > 0 with Geq/Gt is also a union; skip. a < 0 Geq/Gt normalizes
// (flip rel + negate) to a > 0 Leq/Lt.
class MixedQuadraticContractorQ : public ContractorQ {
public:
    MixedQuadraticContractorQ(
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
    mpz_class liveA_;  // scalar coefficient of live^2
    // Term lists for the multivariate coefficients of live^1 (bTerms_)
    // and live^0 (cTerms_). We hold the term shapes here and evaluate
    // them over the runtime rest-box in contract().
    std::vector<PolynomialKernel::MonomialTerm> bTerms_;
    std::vector<PolynomialKernel::MonomialTerm> cTerms_;

    // Sum-of-terms interval evaluation, skipping the live var entry in
    // each term's powers list. Returns nullopt if any rest var is
    // unbounded in the box.
    std::optional<IntervalQ> evalTerms(
        const std::vector<PolynomialKernel::MonomialTerm>& terms,
        const ReasonedBoxQ& box,
        std::vector<SatLit>& usedReasons,
        VarId liveVarId) const;
};

} // namespace xolver
