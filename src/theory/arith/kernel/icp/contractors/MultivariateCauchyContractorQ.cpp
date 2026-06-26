#include "theory/arith/kernel/icp/contractors/MultivariateCauchyContractorQ.h"
#include "theory/arith/kernel/interval/IntervalQOps.h"
#include <algorithm>

namespace xolver {

namespace {

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

MultivariateCauchyContractorQ::MultivariateCauchyContractorQ(
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

    // Partition terms by live exponent. The leading exponent's term must
    // be pure (no rest factors); any mixed live^d term disqualifies V7
    // (would need polynomial coefficient on the leading degree, which
    // breaks the parity argument).
    unsigned maxLiveExp = 0;
    mpz_class leadingASum(0);
    std::unordered_map<unsigned, std::vector<PolynomialKernel::MonomialTerm>> byExp;

    for (const auto& term : *termsOpt) {
        unsigned liveExp = 0;
        bool hasLive = false;
        bool hasOtherVar = false;
        for (const auto& [vid, exp] : term.powers) {
            if (vid == liveVarId) {
                liveExp = static_cast<unsigned>(exp);
                hasLive = true;
            } else {
                hasOtherVar = true;
            }
        }
        if (liveExp > maxLiveExp) maxLiveExp = liveExp;
        (void)hasLive;
        byExp[liveExp].push_back(term);
        (void)hasOtherVar;
    }

    if (maxLiveExp < 2) return;  // degree < 2 → V5c or smaller helpers

    // Leading-exp terms must all be pure live (no rest factors).
    auto leadIt = byExp.find(maxLiveExp);
    if (leadIt == byExp.end()) return;
    for (const auto& term : leadIt->second) {
        for (const auto& [vid, exp] : term.powers) {
            if (vid != liveVarId) {
                // Mixed live^d (e.g. x³·y) — out of V7 scope.
                return;
            }
        }
        leadingASum += term.coefficient;
    }
    if (leadingASum == 0) return;

    // Coexistence with V4: V4 handles "pure live^d + rest" — i.e., when
    // ALL non-leading terms have liveExp == 0 (rest-only). V7 should
    // decline that case so V4's tighter math fires instead.
    bool anyMidLiveTerm = false;
    for (const auto& [exp, terms] : byExp) {
        if (exp > 0 && exp < maxLiveExp && !terms.empty()) {
            anyMidLiveTerm = true;
            break;
        }
    }
    if (!anyMidLiveTerm) return;  // V4's territory

    // Coexistence with V5b (degree exactly 2 with mixed live^1): V5b's
    // discriminant bracket dominates V7's Cauchy. Decline when d == 2.
    if (maxLiveExp == 2) return;

    liveD_ = maxLiveExp;
    liveA_ = std::move(leadingASum);
    // Store non-leading terms (k < d) for runtime evaluation.
    for (auto& [exp, terms] : byExp) {
        if (exp < maxLiveExp) {
            nonLeadingTermsByExp_[exp] = std::move(terms);
        }
    }
    usable_ = true;
}

std::vector<std::string> MultivariateCauchyContractorQ::vars() const {
    return allVars_;
}

SatLit MultivariateCauchyContractorQ::reason() const {
    return constraint_.reason;
}

std::optional<IntervalQ> MultivariateCauchyContractorQ::evalTermsAtExp(
    const std::vector<PolynomialKernel::MonomialTerm>& terms,
    const ReasonedBoxQ& box,
    std::vector<SatLit>& usedReasons,
    VarId liveVarId) const {

    IntervalQ result{mpq_class(0), mpq_class(0)};
    for (const auto& term : terms) {
        mpq_class coeffQ(term.coefficient);
        IntervalQ termInterval{coeffQ, coeffQ};
        for (const auto& [vid, exp] : term.powers) {
            if (vid == liveVarId) continue;  // skip live (already partitioned by exp)
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

ContractorResultQ MultivariateCauchyContractorQ::contract(ReasonedBoxQ& box) {
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

    // Sign-normalize a > 0 by flipping the relation when a < 0.
    Relation rNorm = constraint_.rel;
    mpz_class aAbs = liveA_;
    bool aNegated = false;
    if (liveA_ < 0) {
        aAbs = -liveA_;
        rNorm = flipSign(rNorm);
        aNegated = true;
    }

    // Cauchy: M = 1 + max_k (max(|B_k.lo|, |B_k.hi|) / |a|).
    std::vector<SatLit> restReasons;
    mpq_class maxRatio(0);
    for (const auto& [exp, terms] : nonLeadingTermsByExp_) {
        if (terms.empty()) continue;
        auto intervalOpt = evalTermsAtExp(terms, box, restReasons, liveVarId);
        if (!intervalOpt) {
            return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
        }
        // Account for the sign-normalization flip on all interval coefficients
        // (the Cauchy bound uses abs values so the flip doesn't actually matter,
        // but materializing it would: maxAbs([-lo, -hi]) = max(|lo|, |hi|)).
        (void)aNegated;
        mpq_class absLo = intervalOpt->lo;
        if (absLo < 0) absLo = -absLo;
        mpq_class absHi = intervalOpt->hi;
        if (absHi < 0) absHi = -absHi;
        mpq_class maxAbs = (absLo > absHi) ? absLo : absHi;
        mpq_class aQ(aAbs);
        mpq_class ratio = maxAbs / aQ;
        ratio.canonicalize();
        if (ratio > maxRatio) maxRatio = ratio;
    }
    mpq_class M = mpq_class(1) + maxRatio;
    mpq_class negM(-M);  // materialize

    bool dEven = (liveD_ % 2 == 0);
    const IntervalQ kEmpty{mpq_class(1), mpq_class(0)};

    auto intersect = [&](const mpq_class& lo, const mpq_class& hi) -> IntervalQ {
        mpq_class newLo = std::max(xBox.lo, lo);
        mpq_class newHi = std::min(xBox.hi, hi);
        if (newLo > newHi) return kEmpty;
        return IntervalQ{newLo, newHi};
    };

    std::optional<IntervalQ> newIOpt;
    switch (rNorm) {
        case Relation::Eq:
            newIOpt = intersect(negM, M);
            break;
        case Relation::Leq:
        case Relation::Lt:
            if (dEven) {
                newIOpt = intersect(negM, M);
            } else {
                newIOpt = intersect(xBox.lo, M);
            }
            break;
        case Relation::Geq:
        case Relation::Gt:
            if (dEven) {
                return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
            }
            newIOpt = intersect(negM, xBox.hi);
            break;
        case Relation::Neq:
        default:
            return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    if (!newIOpt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    auto buildReasons = [&]() {
        std::vector<SatLit> reasons = liveRiOpt->reasons;
        reasons.insert(reasons.end(), restReasons.begin(), restReasons.end());
        reasons.push_back(constraint_.reason);
        return reasons;
    };

    const IntervalQ& newI = *newIOpt;
    if (newI.isEmpty()) {
        return ContractorResultQ{
            IcpStatus::Conflict,
            TheoryConflict{buildReasons()},
            {}
        };
    }
    if (newI.lo != xBox.lo || newI.hi != xBox.hi) {
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
