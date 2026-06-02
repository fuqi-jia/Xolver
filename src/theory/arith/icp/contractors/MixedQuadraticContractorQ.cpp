#include "theory/arith/icp/contractors/MixedQuadraticContractorQ.h"
#include "theory/arith/interval/IntervalQOps.h"
#include "theory/arith/interval/IntervalQRoots.h"
#include <algorithm>

namespace xolver {

MixedQuadraticContractorQ::MixedQuadraticContractorQ(
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

    mpz_class aSum(0);
    bool hasLiveSquare = false;
    bool hasLiveLinearMixed = false;
    std::vector<PolynomialKernel::MonomialTerm> bTerms;
    std::vector<PolynomialKernel::MonomialTerm> cTerms;

    for (const auto& term : *termsOpt) {
        int liveExp = 0;
        bool mixedWithLive = false;
        for (const auto& [vid, exp] : term.powers) {
            if (vid == liveVarId) {
                liveExp = exp;
            } else if (term.powers.size() > 1) {
                // Will determine mixedWithLive after the loop based on
                // whether liveVar was also in powers.
            }
        }
        // Recompute "mixed with live" more precisely.
        bool hasLive = false;
        bool hasOtherVar = false;
        for (const auto& [vid, exp] : term.powers) {
            if (vid == liveVarId) hasLive = true;
            else hasOtherVar = true;
        }
        mixedWithLive = hasLive && hasOtherVar;

        if (liveExp >= 3) {
            // Cubic or higher live exponent — out of V5b scope.
            return;
        }

        if (liveExp == 2) {
            if (mixedWithLive) {
                // x²·y-style mixed term — V5b doesn't handle this yet.
                return;
            }
            aSum += term.coefficient;
            hasLiveSquare = true;
        } else if (liveExp == 1) {
            // Pure live (powers = {live}) OR mixed (live + rest vars):
            // either way the term contributes to the linear-in-x
            // coefficient B(rest). For pure live^1 (no rest factors)
            // we still hold the term — evalTerms will just multiply by
            // an empty product = 1.
            bTerms.push_back(term);
            if (mixedWithLive) hasLiveLinearMixed = true;
        } else {
            // liveExp == 0: live-free term, contributes to C(rest).
            cTerms.push_back(term);
        }
    }

    if (!hasLiveSquare) return;       // need at least one live^2 term
    if (aSum == 0) return;             // live^2 coefficients cancelled
    // Coexistence with V4: V4 already handles live^d + g(rest) with no
    // live^1 mixed terms. V5b requires at least one live^1 term to
    // avoid double-coverage. (Pure live^1 alone is fine — V4 wouldn't
    // attempt d=1.)
    if (bTerms.empty()) return;
    // Also require at least one *mixed* live^1 term (live·rest), so V5b
    // genuinely covers the gap. Pure live^1 with no rest factor reduces
    // to univariate ax²+bx+c (V2 territory); the factory may still
    // route here when V2 doesn't fire, but we want to avoid trivial
    // duplication when V2 is already handling the case.
    // Actually: pure live^1 IS in V2's territory only if poly is fully
    // univariate. If poly is multivariate (some other var appears in
    // any term), V2 declines (vars_.size() != 1) and we need V5b to
    // pick up the slack. So we DON'T require mixed live^1 here.
    (void)hasLiveLinearMixed;

    liveA_ = std::move(aSum);
    bTerms_ = std::move(bTerms);
    cTerms_ = std::move(cTerms);
    usable_ = true;
}

std::vector<std::string> MixedQuadraticContractorQ::vars() const {
    return allVars_;
}

SatLit MixedQuadraticContractorQ::reason() const {
    return constraint_.reason;
}

std::optional<IntervalQ> MixedQuadraticContractorQ::evalTerms(
    const std::vector<PolynomialKernel::MonomialTerm>& terms,
    const ReasonedBoxQ& box,
    std::vector<SatLit>& usedReasons,
    VarId liveVarId) const {

    IntervalQ result{mpq_class(0), mpq_class(0)};
    for (const auto& term : terms) {
        mpq_class coeffQ(term.coefficient);
        IntervalQ termInterval{coeffQ, coeffQ};
        for (const auto& [vid, exp] : term.powers) {
            if (vid == liveVarId) continue;  // skip live var
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

ContractorResultQ MixedQuadraticContractorQ::contract(ReasonedBoxQ& box) {
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
    IntervalQ B = *BOpt;
    IntervalQ C = *COpt;

    // Normalize so a > 0.
    Relation r = constraint_.rel;
    mpz_class aPos = liveA_;
    if (liveA_ < 0) {
        switch (r) {
            case Relation::Leq:
            case Relation::Lt:
                // Parabola opens down ⇒ feasible set is a union ⇒ skip.
                return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
            case Relation::Geq:
                r = Relation::Leq;
                break;
            case Relation::Gt:
                r = Relation::Lt;
                break;
            case Relation::Eq:
                // Eq is sign-invariant — just negate the box.
                break;
            default:
                return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
        }
        aPos = -liveA_;
        // Materialize negations explicitly (GMP expression-template gotcha).
        mpq_class newBlo(-B.hi);
        mpq_class newBhi(-B.lo);
        mpq_class newClo(-C.hi);
        mpq_class newChi(-C.lo);
        B = IntervalQ{newBlo, newBhi};
        C = IntervalQ{newClo, newChi};
    }

    // After normalization a > 0. Geq/Gt with a > 0 is still a union; skip.
    if (r == Relation::Geq || r == Relation::Gt) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }
    if (r != Relation::Leq && r != Relation::Lt && r != Relation::Eq) {
        return ContractorResultQ{IcpStatus::NoChange, std::nullopt, {}};
    }

    // B² interval — straddle-zero corner matters: min B² = 0 when 0 ∈ [Bl, Bh].
    mpq_class BloSq(B.lo * B.lo);
    mpq_class BhiSq(B.hi * B.hi);
    mpq_class BsqMax = std::max(BloSq, BhiSq);
    mpq_class BsqMin;
    if (B.lo <= 0 && B.hi >= 0) {
        BsqMin = mpq_class(0);
    } else {
        BsqMin = std::min(BloSq, BhiSq);
    }

    // disc range. With a > 0: 4aC range = [4a·C.lo, 4a·C.hi], so disc range
    // is [BsqMin − 4a·C.hi, BsqMax − 4a·C.lo].
    mpq_class fourAq(4 * aPos);
    mpq_class discMin = BsqMin - fourAq * C.hi;
    mpq_class discMax = BsqMax - fourAq * C.lo;

    auto buildReasons = [&]() {
        std::vector<SatLit> reasons = liveRiOpt->reasons;
        reasons.insert(reasons.end(), restReasons.begin(), restReasons.end());
        reasons.push_back(constraint_.reason);
        return reasons;
    };

    if (discMax < 0) {
        // No real solutions for ANY (B, C) ⇒ Conflict (Leq/Lt/Eq all unsat).
        return ContractorResultQ{
            IcpStatus::Conflict,
            TheoryConflict{buildReasons()},
            {}
        };
    }

    // Outward √(max disc). If discMax ≥ 0 but small, sqrtCeil ≥ true.
    mpq_class sqrtDiscMax = mpqSqrtCeil(discMax);

    // min r1 = (-B.hi - sqrtDiscMax) / (2a). Materialize negation.
    mpq_class twoA(2 * aPos);
    mpq_class negBhi(-B.hi);
    mpq_class negBlo(-B.lo);
    mpq_class r1LoNum = negBhi - sqrtDiscMax;
    mpq_class r2HiNum = negBlo + sqrtDiscMax;
    mpq_class r1Lo = r1LoNum / twoA;
    mpq_class r2Hi = r2HiNum / twoA;
    r1Lo.canonicalize();
    r2Hi.canonicalize();

    mpq_class newLo = std::max(xBox.lo, r1Lo);
    mpq_class newHi = std::min(xBox.hi, r2Hi);

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
