#include "theory/arith/kernel/icp/contractors/MonomialMultivariateContractorQ.h"
#include "theory/arith/kernel/interval/IntervalQOps.h"
#include "theory/arith/kernel/interval/IntervalQRoots.h"
#include <algorithm>

namespace xolver {

namespace {

// Flip so that `p rel 0` becomes equivalent after negating p. Eq/Neq are
// sign-invariant. Duplicated from RelationContractorQ's anon-ns helper to
// avoid coupling files; the two-line switch isn't worth a shared header.
Relation flipSign(Relation r) {
    switch (r) {
        case Relation::Leq: return Relation::Geq;
        case Relation::Geq: return Relation::Leq;
        case Relation::Lt:  return Relation::Gt;
        case Relation::Gt:  return Relation::Lt;
        default:            return r;
    }
}

} // namespace

MonomialMultivariateContractorQ::MonomialMultivariateContractorQ(
    const IcpConstraint& constraint,
    PolynomialKernel& kernel,
    const std::string& liveVar)
    : constraint_(constraint), kernel_(kernel), liveVar_(liveVar) {

    allVars_ = kernel_.variables(constraint_.poly);

    auto liveVarIdOpt = kernel_.findVar(liveVar_);
    if (!liveVarIdOpt) return;
    VarId liveVarId = *liveVarIdOpt;

    auto termsOpt = kernel_.terms(constraint_.poly);
    if (!termsOpt) return;

    // Partition into (live, rest). Mixed terms — a single monomial containing
    // liveVar AND another variable — reject the shape: this contractor's math
    // assumes the live var's coefficient is a scalar.
    bool foundLive = false;
    mpz_class liveACandidate(0);
    unsigned liveDCandidate = 0;
    std::vector<PolynomialKernel::MonomialTerm> restCandidate;

    for (const auto& term : *termsOpt) {
        bool involvesLive = false;
        int liveExp = 0;
        for (const auto& [vid, exp] : term.powers) {
            if (vid == liveVarId) {
                involvesLive = true;
                liveExp = exp;
                break;
            }
        }

        if (involvesLive) {
            // Must be a pure live monomial — no other variables in this term.
            if (term.powers.size() != 1) return;
            // V4 minimal scope: all live-degree terms must share a single d.
            // (Mixed-degree like x³ + x would need a more general univariate
            // root-finder; treat as not-this-contractor for now.)
            if (foundLive) {
                if (liveDCandidate != static_cast<unsigned>(liveExp)) return;
                liveACandidate += term.coefficient;
            } else {
                liveACandidate = term.coefficient;
                liveDCandidate = static_cast<unsigned>(liveExp);
                foundLive = true;
            }
        } else {
            restCandidate.push_back(term);
        }
    }

    if (!foundLive) return;        // poly doesn't actually depend on liveVar
    if (liveDCandidate < 2) return; // d < 2 is linear; out of V4 scope
    if (liveACandidate == 0) return;

    liveA_ = std::move(liveACandidate);
    liveD_ = liveDCandidate;
    restTerms_ = std::move(restCandidate);
    usable_ = true;
}

std::vector<std::string> MonomialMultivariateContractorQ::vars() const {
    return allVars_;
}

SatLit MonomialMultivariateContractorQ::reason() const {
    return constraint_.reason;
}

std::optional<IntervalQ> MonomialMultivariateContractorQ::evalRest(
    const ReasonedBoxQ& box,
    std::vector<SatLit>& usedReasons) const {

    IntervalQ result{mpq_class(0), mpq_class(0)};
    for (const auto& term : restTerms_) {
        mpq_class coeffQ(term.coefficient);
        IntervalQ termInterval{coeffQ, coeffQ};

        for (const auto& [vid, exp] : term.powers) {
            std::string name(kernel_.varName(vid));
            auto riOpt = box.get(name);
            if (!riOpt) return std::nullopt;  // unbounded rest var: bail

            for (const auto& reason : riOpt->reasons) {
                usedReasons.push_back(reason);
            }

            IntervalQ varPow = intervalQPow(riOpt->interval,
                                            static_cast<uint32_t>(exp));
            termInterval = intervalQMul(termInterval, varPow);
        }
        result = intervalQAdd(result, termInterval);
    }
    return result;
}

std::optional<IntervalQ> MonomialMultivariateContractorQ::applyMonomialBound(
    const mpz_class& a, unsigned d, const mpq_class& cEff,
    Relation rel, const IntervalQ& xBox) const {

    // Normalize the leading coefficient to positive by flipping rel. This
    // mirrors V2/V3's a > 0 normalization — keeps the case-split below
    // single-quadrant in (d parity, sign T).
    Relation r = rel;
    mpz_class aPos = a;
    mpq_class effC = cEff;
    if (a < 0) {
        r = flipSign(rel);
        aPos = -a;
        effC = -cEff;
    }
    mpq_class aQ(aPos);
    mpq_class T = -effC / aQ;
    T.canonicalize();

    const IntervalQ kEmpty{mpq_class(1), mpq_class(0)};

    auto rootCeil = [d](const mpq_class& t) -> mpq_class {
        if (t >= 0) return mpqRootCeil(t, d);
        return -mpqRootFloor(-t, d);
    };
    auto rootFloor = [d](const mpq_class& t) -> mpq_class {
        if (t >= 0) return mpqRootFloor(t, d);
        return -mpqRootCeil(-t, d);
    };

    if (d % 2 == 0) {
        // Even d: x^d ≥ 0.
        if (T < 0) {
            switch (r) {
                case Relation::Leq:
                case Relation::Lt:
                case Relation::Eq:
                    return kEmpty;
                default:
                    return std::nullopt;
            }
        }
        switch (r) {
            case Relation::Leq:
            case Relation::Lt: {
                mpq_class rt = mpqRootCeil(T, d);
                mpq_class negRt(-rt);
                mpq_class lo = std::max(xBox.lo, negRt);
                mpq_class hi = std::min(xBox.hi, rt);
                if (lo > hi) return kEmpty;
                return IntervalQ{lo, hi};
            }
            case Relation::Geq:
            case Relation::Gt:
                // |x| ≥ T^(1/d) is a union of two unbounded sets ⇒ skip.
                return std::nullopt;
            case Relation::Eq:
            case Relation::Neq:
                return std::nullopt;
            default:
                return std::nullopt;
        }
    }

    // Odd d.
    switch (r) {
        case Relation::Leq:
        case Relation::Lt: {
            mpq_class rt = rootCeil(T);
            mpq_class hi = std::min(xBox.hi, rt);
            if (xBox.lo > hi) return kEmpty;
            return IntervalQ{xBox.lo, hi};
        }
        case Relation::Geq:
        case Relation::Gt: {
            mpq_class rt = rootFloor(T);
            mpq_class lo = std::max(xBox.lo, rt);
            if (lo > xBox.hi) return kEmpty;
            return IntervalQ{lo, xBox.hi};
        }
        default:
            return std::nullopt;
    }
}

ContractorResultQ MonomialMultivariateContractorQ::contract(ReasonedBoxQ& box) {
    if (!usable_) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    auto liveRiOpt = box.get(liveVar_);
    if (!liveRiOpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }
    const IntervalQ xInterval = liveRiOpt->interval;

    std::vector<SatLit> restReasons;
    auto gBoxOpt = evalRest(box, restReasons);
    if (!gBoxOpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }
    const IntervalQ& gBox = *gBoxOpt;

    // c_eff selection — Leq/Lt project against the loosest possible rhs (so
    // the bound on a·x^d is `≤ -gBox.lo`), Geq/Gt against the tightest. Eq
    // is bidirectional: a·x^d + g = 0 ⇒ a·x^d ∈ [-gBox.hi, -gBox.lo], which
    // we realize as two independent single-sided projections (Leq w/
    // cEff=gBox.lo AND Geq w/ cEff=gBox.hi) intersected with xBox. Either
    // projection may decline (nullopt) — for even-d Geq the lower side is
    // always a union and adds nothing, for example — and we still use the
    // other side when at least one fires.
    std::optional<IntervalQ> newIOpt;
    switch (constraint_.rel) {
        case Relation::Leq:
        case Relation::Lt:
            newIOpt = applyMonomialBound(liveA_, liveD_, gBox.lo,
                                          constraint_.rel, xInterval);
            break;
        case Relation::Geq:
        case Relation::Gt:
            newIOpt = applyMonomialBound(liveA_, liveD_, gBox.hi,
                                          constraint_.rel, xInterval);
            break;
        case Relation::Eq: {
            auto upper = applyMonomialBound(liveA_, liveD_, gBox.lo,
                                             Relation::Leq, xInterval);
            auto lower = applyMonomialBound(liveA_, liveD_, gBox.hi,
                                             Relation::Geq, xInterval);
            if (!upper && !lower) break;  // newIOpt stays nullopt
            IntervalQ cand = xInterval;
            bool empty = false;
            auto fold = [&](const std::optional<IntervalQ>& side) {
                if (!side) return;
                if (side->isEmpty()) { empty = true; return; }
                cand.lo = std::max(cand.lo, side->lo);
                cand.hi = std::min(cand.hi, side->hi);
            };
            fold(upper);
            if (!empty) fold(lower);
            if (empty || cand.lo > cand.hi) {
                newIOpt = IntervalQ{mpq_class(1), mpq_class(0)};
            } else {
                newIOpt = cand;
            }
            break;
        }
        case Relation::Neq:
        default:
            return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    if (!newIOpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    // Reasons union: liveVar's bounds + rest-var bounds + the constraint
    // literal. Anything that *could* have changed the answer needs to be
    // in the conflict explanation.
    std::vector<SatLit> reasons = liveRiOpt->reasons;
    reasons.insert(reasons.end(), restReasons.begin(), restReasons.end());
    reasons.push_back(constraint_.reason);

    const IntervalQ& newI = *newIOpt;
    if (newI.isEmpty()) {
        return ContractorResultQ{
            IcpStatus::Conflict,
            TheoryConflict{reasons},
            {}
        };
    }
    if (newI.lo != xInterval.lo || newI.hi != xInterval.hi) {
        box.narrow(liveVar_, newI, reasons);
        BoundUpdateQ update{liveVar_, newI, reasons};
        return ContractorResultQ{
            IcpStatus::DomainUpdate,
            std::nullopt,
            {update}
        };
    }

    return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
}

} // namespace xolver
