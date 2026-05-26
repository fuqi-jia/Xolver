#include "theory/arith/icp/contractors/SquareContractorZ.h"
#include "theory/arith/interval/IntervalOperations.h"
#include <cmath>

namespace zolver {

SquareContractorZ::SquareContractorZ(const IcpConstraint& constraint, PolynomialKernel& kernel)
    : constraint_(constraint), kernel_(kernel) {
    vars_ = kernel_.variables(constraint_.poly);
}

bool SquareContractorZ::recognizePattern(int& sign, mpz_class& c) const {
    if (vars_.size() != 1) return false;

    auto degOpt = kernel_.degree(constraint_.poly, vars_[0]);
    if (!degOpt || *degOpt != 2) return false;

    auto coeffsOpt = kernel_.getIntegerCoefficients(constraint_.poly, vars_[0]);
    if (!coeffsOpt || coeffsOpt->size() != 3) return false;

    const auto& coeffs = *coeffsOpt;
    // coeffs: [a2, a1, a0] for a2*x^2 + a1*x + a0
    if (coeffs[1] != 0) return false; // linear term must be zero

    if (coeffs[0] == 1) {
        sign = 1;
        c = -coeffs[2]; // x^2 - c => a0 = -c
        return true;
    }
    if (coeffs[0] == -1) {
        sign = -1;
        c = coeffs[2]; // -x^2 + c => a0 = c
        return true;
    }
    return false;
}

ContractorResultZ SquareContractorZ::contract(ReasonedBoxZ& box) {
    int sign;
    mpz_class c;
    if (!recognizePattern(sign, c)) {
        return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
    }

    const std::string& var = vars_[0];
    std::vector<SatLit> reasons;
    auto riOpt = box.get(var);
    if (riOpt) {
        reasons = riOpt->reasons;
    }
    reasons.push_back(constraint_.reason);

    Relation rel = constraint_.rel;

    // Normalize: we handle p = x^2 - c (sign=1) or p = -x^2 + c (sign=-1)
    // For sign=-1, invert relation to match x^2 - c form
    if (sign == -1) {
        switch (rel) {
            case Relation::Leq: rel = Relation::Geq; break;
            case Relation::Geq: rel = Relation::Leq; break;
            case Relation::Lt:  rel = Relation::Gt;  break;
            case Relation::Gt:  rel = Relation::Lt;  break;
            default: break; // Eq, Neq unchanged
        }
        c = -c; // now treating as x^2 - (-c)
    }

    // Now rel applies to x^2 - c
    switch (rel) {
        case Relation::Leq: // x^2 <= c
            if (c < 0) {
                return ContractorResultZ{IcpStatus::Conflict, TheoryConflict{reasons}, {}};
            }
            if (c >= 0) {
                mpz_class r;
                mpz_sqrt(r.get_mpz_t(), c.get_mpz_t());
                // floor_sqrt: if r*r > c, decrement
                while (r * r > c) --r;
                return ContractorResultZ{
                    IcpStatus::DomainUpdate,
                    std::nullopt,
                    {{var, IntervalZ{-r, r}, reasons}}
                };
            }
            break;

        case Relation::Geq: // x^2 >= c
            if (c < 0) {
                return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}}; // tautology
            }
            // V1: no interval contraction for x^2 >= c with c >= 0
            return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};

        case Relation::Eq: // x^2 = c
            if (c < 0) {
                return ContractorResultZ{IcpStatus::Conflict, TheoryConflict{reasons}, {}};
            }
            {
                mpz_class r;
                mpz_sqrt(r.get_mpz_t(), c.get_mpz_t());
                while (r * r > c) --r;
                if (r * r != c) {
                    // Not a perfect square -> Empty for integers
                    return ContractorResultZ{IcpStatus::Conflict, TheoryConflict{reasons}, {}};
                }
                // V1: interval update only; exact finite-set {-r,r} stays in old SquareBoundReasoner
                return ContractorResultZ{
                    IcpStatus::DomainUpdate,
                    std::nullopt,
                    {{var, IntervalZ{-r, r}, reasons}}
                };
            }

        case Relation::Neq: // x^2 != c
            if (c < 0) {
                return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}}; // tautology
            }
            return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};

        default:
            return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
    }

    return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
}

std::vector<std::string> SquareContractorZ::vars() const {
    return vars_;
}

SatLit SquareContractorZ::reason() const {
    return constraint_.reason;
}

} // namespace zolver
