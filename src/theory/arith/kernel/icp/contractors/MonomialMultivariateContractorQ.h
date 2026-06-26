#pragma once

#include "theory/arith/kernel/icp/Contractor.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include <gmpxx.h>
#include <string>
#include <vector>

namespace xolver {

// V4 — multivariate monomial contractor.
//
// Targets polynomials of the shape `a · liveVar^d + g(rest) rel 0`, where
//   - a is a scalar integer coefficient,
//   - d ≥ 2 (V1/V2/V3 handle d ≤ 1 / pure univariate),
//   - g(rest) is an arbitrary polynomial in variables other than liveVar
//     (no monomial mixes liveVar with another variable).
//
// At construction time we partition the polynomial's monomial terms into
//   • the *live* terms (powers of liveVar alone), and
//   • the *rest* terms (no liveVar appearance).
// Mixed terms (e.g. x·y in a constraint with liveVar = x) immediately
// disqualify the constraint for this contractor; `isUsable()` returns
// false and contract() becomes a no-op. The factory should skip
// non-usable instances.
//
// Soundness (Leq direction): the original constraint holds for some y in
// y_box iff a·x^d ≤ max_y(−g(y)) = −min_y g(y). Interval evaluation
// over-approximates: min_y g(y) ≥ gBox.lo, so −min_y g(y) ≤ −gBox.lo.
// We narrow x using the loosest valid bound `a·x^d ≤ −gBox.lo`, which
// over-approximates the true feasible x-set — sound but possibly less
// tight than ideal. Geq is symmetric (uses gBox.hi). Eq is bidirectional
// and deferred for now; Neq isn't single-interval representable.
//
// vars() returns ALL polynomial variables so the engine refires this
// contractor whenever any rest variable's bound tightens. Each (poly,
// liveVar) pair is its own contractor; multiple V4 instances per
// constraint (one per candidate live var) is the factory's job.
class MonomialMultivariateContractorQ : public ContractorQ {
public:
    MonomialMultivariateContractorQ(
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
    mpz_class liveA_;
    unsigned liveD_ = 0;
    std::vector<PolynomialKernel::MonomialTerm> restTerms_;

    // Sound interval evaluation of g(rest) over `box`. Returns nullopt if
    // any rest variable is unbounded in the box — the contractor then
    // backs off rather than relaxing to an infinite interval.
    std::optional<IntervalQ> evalRest(const ReasonedBoxQ& box,
                                       std::vector<SatLit>& usedReasons) const;

    // Apply degree-d narrowing for `a · x^d + cEff rel 0` (b == 0 case),
    // mirroring V2/V3's discriminant / d-th-root math. Returns nullopt
    // if not applicable (the (rel, parity, sign-T) combination is a
    // union or vacuous); an empty IntervalQ signals constraint
    // unsatisfiable; a non-empty IntervalQ is the result already
    // intersected with xBox.
    std::optional<IntervalQ> applyMonomialBound(
        const mpz_class& a, unsigned d, const mpq_class& cEff,
        Relation rel, const IntervalQ& xBox) const;
};

} // namespace xolver
