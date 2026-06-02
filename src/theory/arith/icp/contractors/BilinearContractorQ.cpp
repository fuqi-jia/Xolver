#include "theory/arith/icp/contractors/BilinearContractorQ.h"
#include "theory/arith/interval/IntervalQOps.h"
#include <algorithm>

namespace xolver {

namespace {

// Invert a sign-pinned interval B. Precondition: Bl > 0 OR Bh < 0
// (caller checks 0 ∉ B). For B > 0: 1/B ∈ [1/B.hi, 1/B.lo] (both
// positive). For B < 0: 1/B ∈ [1/B.hi, 1/B.lo] (both negative — note
// 1/B is order-reversing when B is negative too, but division by neg
// flips: 1/(more negative) is less negative, so the same formula holds).
IntervalQ intervalInvert(const IntervalQ& B) {
    mpq_class invHi(1);
    invHi /= B.lo;
    mpq_class invLo(1);
    invLo /= B.hi;
    invHi.canonicalize();
    invLo.canonicalize();
    return IntervalQ{invLo, invHi};
}

} // namespace

BilinearContractorQ::BilinearContractorQ(
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

    std::vector<PolynomialKernel::MonomialTerm> bTerms;
    std::vector<PolynomialKernel::MonomialTerm> cTerms;
    bool sawLive = false;

    for (const auto& term : *termsOpt) {
        int liveExp = 0;
        for (const auto& [vid, exp] : term.powers) {
            if (vid == liveVarId) {
                liveExp = exp;
                break;
            }
        }
        if (liveExp >= 2) {
            // V4/V5b territory — V5c only handles linear-in-live.
            return;
        }
        if (liveExp == 1) {
            bTerms.push_back(term);
            sawLive = true;
        } else {
            cTerms.push_back(term);
        }
    }

    if (!sawLive) return;  // poly doesn't depend on liveVar

    bTerms_ = std::move(bTerms);
    cTerms_ = std::move(cTerms);
    usable_ = true;
}

std::vector<std::string> BilinearContractorQ::vars() const {
    return allVars_;
}

SatLit BilinearContractorQ::reason() const {
    return constraint_.reason;
}

std::optional<IntervalQ> BilinearContractorQ::evalTerms(
    const std::vector<PolynomialKernel::MonomialTerm>& terms,
    const ReasonedBoxQ& box,
    std::vector<SatLit>& usedReasons,
    VarId liveVarId) const {

    IntervalQ result{mpq_class(0), mpq_class(0)};
    for (const auto& term : terms) {
        mpq_class coeffQ(term.coefficient);
        IntervalQ termInterval{coeffQ, coeffQ};
        for (const auto& [vid, exp] : term.powers) {
            if (vid == liveVarId) continue;
            std::string name(kernel_.varName(vid));
            auto riOpt = box.get(name);
            if (!riOpt) return std::nullopt;
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

ContractorResultQ BilinearContractorQ::contract(ReasonedBoxQ& box) {
    if (!usable_) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    auto liveRiOpt = box.get(liveVar_);
    if (!liveRiOpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }
    const IntervalQ xBox = liveRiOpt->interval;

    auto liveVarIdOpt = kernel_.findVar(liveVar_);
    if (!liveVarIdOpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }
    VarId liveVarId = *liveVarIdOpt;

    std::vector<SatLit> restReasons;
    auto BOpt = evalTerms(bTerms_, box, restReasons, liveVarId);
    auto COpt = evalTerms(cTerms_, box, restReasons, liveVarId);
    if (!BOpt || !COpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }
    const IntervalQ B = *BOpt;
    const IntervalQ C = *COpt;

    // 0 ∈ B ⇒ 1/B undefined; bail.
    if (B.lo <= 0 && B.hi >= 0) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    // D = -C, materialized.
    mpq_class negChi(-C.lo);
    mpq_class negClo(-C.hi);
    IntervalQ D{negClo, negChi};

    // 1/B (well-defined because B is sign-pinned).
    IntervalQ invB = intervalInvert(B);

    // r = D · (1/B). The "feasible x set" depends on the rel:
    //   B > 0, Leq: B·x + C ≤ 0 ⇔ x ≤ D/B → upper-bound x via max(r).
    //   B > 0, Geq: x ≥ D/B → lower-bound x via min(r).
    //   B < 0, Leq: x ≥ D/B → lower-bound x via min(r).
    //   B < 0, Geq: x ≤ D/B → upper-bound x via max(r).
    //   Eq: x = D/B → bracket [min(r), max(r)].
    IntervalQ r = intervalQMul(D, invB);

    bool BPositive = (B.lo > 0);

    auto buildReasons = [&]() {
        std::vector<SatLit> reasons = liveRiOpt->reasons;
        reasons.insert(reasons.end(), restReasons.begin(), restReasons.end());
        reasons.push_back(constraint_.reason);
        return reasons;
    };

    Relation rel = constraint_.rel;
    mpq_class newLo = xBox.lo;
    mpq_class newHi = xBox.hi;

    auto applyUpperBound = [&](const mpq_class& ub) {
        if (ub < newHi) newHi = ub;
    };
    auto applyLowerBound = [&](const mpq_class& lb) {
        if (lb > newLo) newLo = lb;
    };

    switch (rel) {
        case Relation::Leq:
        case Relation::Lt:
            if (BPositive) applyUpperBound(r.hi);
            else           applyLowerBound(r.lo);
            break;
        case Relation::Geq:
        case Relation::Gt:
            if (BPositive) applyLowerBound(r.lo);
            else           applyUpperBound(r.hi);
            break;
        case Relation::Eq:
            applyLowerBound(r.lo);
            applyUpperBound(r.hi);
            break;
        case Relation::Neq:
        default:
            return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    if (newLo > newHi) {
        return ContractorResultQ{
            IcpStatus::Conflict,
            TheoryConflict{buildReasons()},
            {}
        };
    }

    if (newLo != xBox.lo || newHi != xBox.hi) {
        IntervalQ newI{newLo, newHi};
        std::vector<SatLit> reasons = buildReasons();
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
