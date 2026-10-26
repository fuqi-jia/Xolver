#include "search/icp/contractors/RelationContractor.h"
#include "algebra/interval/IntervalEvaluator.h"
#include <algorithm>
#include <map>

namespace xolver {

RelationContractor::RelationContractor(const IcpConstraint& constraint, PolynomialKernel& kernel)
    : constraint_(constraint), kernel_(kernel) {
    vars_ = kernel_.variables(constraint_.poly);
    if (vars_.size() > 1) terms_ = kernel_.terms(constraint_.poly);
    if (terms_) {
        // Compile isolatable coordinates once. Repeated contractions only
        // evaluate their changing interval premises, never rescan structure.
        struct Occurrence { bool seen = false, blocked = false; mpz_class coefficient = 0; };
        std::map<VarId, Occurrence> occurrences;
        for (const auto& term : *terms_) for (const auto& [variable, exponent] : term.powers) {
            auto& entry = occurrences[variable];
            if (entry.seen || term.powers.size() != 1 || exponent != 1) entry.blocked = true;
            entry.seen = true;
            entry.coefficient = term.coefficient;
        }
        for (const auto& [variable, entry] : occurrences)
            if (!entry.blocked && entry.coefficient != 0)
                projections_.push_back({variable, entry.coefficient});
    }
}

ContractorResultZ RelationContractor::contract(ReasonedBox& box) {
    if (vars_.size() != 1) {
        IntervalEvaluator evaluator(kernel_);
        const auto forward = evaluator.run({constraint_.poly, constraint_.rel, constraint_.reason}, box);
        if (forward.status == IntervalEvalStatus::DefinitelyViolated) {
            auto reasons = forward.usedReasons;
            reasons.push_back(constraint_.reason);
            return {IcpStatus::Conflict, TheoryConflict{std::move(reasons)}, {}};
        }
        // Z contraction rounds endpoints to integers. A real-valued client
        // may use the forward enclosure, but must use the Q contractor for
        // backward bounds; integer rounding would discard fractional models.
        const bool integerOwner = constraint_.owner == TheoryId::NIA ||
            constraint_.owner == TheoryId::LIA || constraint_.owner == TheoryId::IDL;
        if (!terms_ || constraint_.rel == Relation::Neq || !integerOwner)
            return {IcpStatus::NoChange, std::nullopt, {}};
        std::vector<BoundUpdateZ> updates;
        for (const auto& [coordinate, coefficient] : projections_) {
            const std::string name(kernel_.varName(coordinate));
            auto rest = evaluator.evaluateTerms(*terms_, box, coordinate);
            if (!rest) continue;
            auto current = box.get(name);
            if (!current && constraint_.rel != Relation::Eq) continue;
            IntervalZ narrowed = current ? current->interval : IntervalZ{0, 0};
            auto divide = [&](const mpz_class& numerator, bool ceiling) {
                mpz_class result;
                if (ceiling) mpz_cdiv_q(result.get_mpz_t(), numerator.get_mpz_t(), coefficient.get_mpz_t());
                else mpz_fdiv_q(result.get_mpz_t(), numerator.get_mpz_t(), coefficient.get_mpz_t());
                return result;
            };
            auto lower = [&](const mpz_class& bound) { narrowed.lo = current ? std::max(narrowed.lo, bound) : bound; };
            auto upper = [&](const mpz_class& bound) { narrowed.hi = current ? std::min(narrowed.hi, bound) : bound; };
            if (constraint_.rel == Relation::Eq) {
                lower(divide(coefficient > 0 ? mpz_class(-rest->interval.hi) : mpz_class(-rest->interval.lo), true));
                upper(divide(coefficient > 0 ? mpz_class(-rest->interval.lo) : mpz_class(-rest->interval.hi), false));
            } else if (constraint_.rel == Relation::Leq || constraint_.rel == Relation::Lt) {
                const mpz_class rhs = -rest->interval.lo - (constraint_.rel == Relation::Lt ? 1 : 0);
                if (coefficient > 0) upper(divide(rhs, false));
                else lower(divide(rhs, true));
            } else if (constraint_.rel == Relation::Geq || constraint_.rel == Relation::Gt) {
                const mpz_class rhs = -rest->interval.hi + (constraint_.rel == Relation::Gt ? 1 : 0);
                if (coefficient > 0) lower(divide(rhs, true));
                else upper(divide(rhs, false));
            }
            if (current && narrowed.lo == current->interval.lo && narrowed.hi == current->interval.hi) continue;
            rest->reasons.push_back(constraint_.reason);
            if (current) rest->reasons.insert(rest->reasons.end(), current->reasons.begin(), current->reasons.end());
            if (narrowed.isEmpty()) return {IcpStatus::Conflict, TheoryConflict{std::move(rest->reasons)}, {}};
            updates.push_back({name, std::move(narrowed), std::move(rest->reasons)});
        }
        if (!updates.empty()) return {IcpStatus::DomainUpdate, std::nullopt, std::move(updates)};
        return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
    }

    const std::string& var = vars_[0];
    auto riOpt = box.get(var);
    if (!riOpt) {
        return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
    }

    auto degOpt = kernel_.degree(constraint_.poly, var);
    if (!degOpt) {
        return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
    }

    auto coeffsOpt = kernel_.getIntegerCoefficients(constraint_.poly, var);
    if (!coeffsOpt) {
        return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
    }

    const auto& coeffs = *coeffsOpt;
    const IntervalZ& xInterval = riOpt->interval;

    // Evaluate polynomial at interval
    IntervalZ result{mpz_class(0), mpz_class(0)};
    for (size_t i = 0; i < coeffs.size(); ++i) {
        const mpz_class& coeff = coeffs[i];
        if (coeff == 0) continue;
        size_t power = coeffs.size() - 1 - i;
        IntervalZ termInterval = intervalPow(xInterval, static_cast<uint32_t>(power));
        if (coeff != 1) {
            IntervalZ coeffInterval{coeff, coeff};
            termInterval = intervalMul(coeffInterval, termInterval);
        }
        result = intervalAdd(result, termInterval);
    }

    // Collect reasons
    std::vector<SatLit> reasons = riOpt->reasons;
    reasons.push_back(constraint_.reason);

    if (isDefinitelyViolated(result, constraint_.rel)) {
        return ContractorResultZ{
            IcpStatus::Conflict,
            TheoryConflict{reasons},
            {}
        };
    }

    return ContractorResultZ{IcpStatus::NoChange, std::nullopt, {}};
}

std::vector<std::string> RelationContractor::vars() const {
    return vars_;
}

SatLit RelationContractor::reason() const {
    return constraint_.reason;
}

bool RelationContractor::isDefinitelyViolated(const IntervalZ& polyInterval, Relation rel) const {
    switch (rel) {
        case Relation::Leq:
            return polyInterval.lo > 0;
        case Relation::Geq:
            return polyInterval.hi < 0;
        case Relation::Eq:
            return !polyInterval.containsZero();
        case Relation::Neq:
            return polyInterval.lo == 0 && polyInterval.hi == 0;
        default:
            return false; // Lt/Gt: V1 not handled here (normalized before ICP for NIA, NoChange for NRA)
    }
}

} // namespace xolver
