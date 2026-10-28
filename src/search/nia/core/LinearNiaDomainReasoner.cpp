#include "search/nia/core/LinearNiaDomainReasoner.h"
#include "search/linear/LinearBoundPropagation.h"

namespace xolver {

LinearNiaDomainReasoner::LinearNiaDomainReasoner(PolynomialKernel& kernel)
    : kernel_(kernel) {}

bool LinearNiaDomainReasoner::extractLinearForm(
    PolyId poly, mpz_class& a, mpz_class& c, std::string& var) const {

    a = 0;
    c = 0;
    var.clear();

    auto vars = kernel_.variables(poly);
    if (vars.size() != 1) return false;
    var = vars[0];

    auto degOpt = kernel_.degree(poly, var);
    if (!degOpt) return false;
    int deg = *degOpt;
    if (deg > 1) return false;

    auto coeffsOpt = kernel_.getIntegerCoefficients(poly, var);
    if (!coeffsOpt) return false;
    const auto& coeffs = *coeffsOpt;
    if (coeffs.size() != 2) {
        // Could be constant (degree 0)
        if (coeffs.size() == 1) {
            c = coeffs[0];
            a = 0;
            return true;
        }
        return false;
    }

    // coeffs: [leading, constant]
    a = coeffs[0];
    c = coeffs[1];
    return true;
}

NiaReasoningResult LinearNiaDomainReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints,
    DomainStore& domains) {

    bool updated = false;

    for (const auto& c : constraints) {
        mpz_class a, coeff_c;
        std::string var;
        if (!extractLinearForm(c.poly, a, coeff_c, var)) continue;

        if (a == 0) {
            // Constant constraint: c rel 0
            // Should have been handled by trivial constant check
            continue;
        }

        // a*x + c rel 0  =>  a*x rel -c
        mpz_class neg_c = -coeff_c;

        switch (c.rel) {
            case Relation::Leq: {
                // a*x + c <= 0  =>  a*x <= -c  =>  x <= floor(-c/a)  if a>0
                //                                            x >= ceil(-c/a) if a<0
                mpz_class q = neg_c / a;
                mpz_class r = neg_c % a;
                if (a > 0) {
                    // floor division: if remainder has opposite sign to a, adjust down
                    if (r < 0) { q -= 1; }
                    domains.addUpperBound(var, q, c.reason);
                } else {
                    // ceil division: if non-zero and quotient positive, adjust up
                    if (r != 0 && ((neg_c > 0) == (a > 0))) {
                        q += 1;
                    }
                    domains.addLowerBound(var, q, c.reason);
                }
                updated = true;
                break;
            }
            case Relation::Geq: {
                // a*x + c >= 0  =>  a*x >= -c  =>  x >= ceil(-c/a)  if a>0
                //                                            x <= floor(-c/a) if a<0
                mpz_class q = neg_c / a;
                mpz_class r = neg_c % a;
                if (a > 0) {
                    // ceil division
                    if (r != 0 && ((neg_c > 0) == (a > 0))) {
                        q += 1;
                    }
                    domains.addLowerBound(var, q, c.reason);
                } else {
                    // floor division
                    if (r != 0 && ((neg_c > 0) != (a > 0))) {
                        q -= 1;
                    }
                    domains.addUpperBound(var, q, c.reason);
                }
                updated = true;
                break;
            }
            case Relation::Eq: {
                if (neg_c % a == 0) {
                    mpz_class val = neg_c / a;
                    domains.restrictToFiniteSet(var, {val}, c.reason);
                    updated = true;
                } else {
                    // No integer solution
                    return {NiaReasoningKind::Conflict,
                            TheoryConflict{{c.reason}},
                            std::nullopt};
                }
                break;
            }
            case Relation::Neq: {
                if (neg_c % a == 0) {
                    mpz_class val = neg_c / a;
                    domains.excludeValue(var, val, c.reason);
                    updated = true;
                }
                // a*x + c != 0 with no integer root: tautology
                break;
            }
            default:
                break;
        }
    }

    // Propagate general affine rows to a fixpoint before bounded search.
    // The shared engine carries every row and endpoint guard, including through
    // chains whose defining rows occur in reverse dependency order.
    std::vector<LinearBoundRow> rows;
    for (const auto& constraint : constraints) {
        if (constraint.rel == Relation::Neq) continue;
        const auto terms = kernel_.terms(constraint.poly);
        if (!terms) continue;
        LinearBoundRow row{{}, constraint.rel, 0, {constraint.reason}};
        bool linear = true;
        for (const auto& term : *terms) {
            if (term.powers.empty()) row.rhs -= term.coefficient;
            else if (term.powers.size() == 1 && term.powers[0].second == 1)
                row.lhs.terms.emplace_back(std::string(kernel_.varName(term.powers[0].first)),
                                           term.coefficient);
            else {
                linear = false;
                break;
            }
        }
        // Single-variable constraints were already consumed above.
        if (linear && row.lhs.terms.size() > 1) rows.push_back(std::move(row));
    }
    WorkBudget aggregateBudget(262144);
    if (const auto conflict = LinearBoundPropagation::aggregateConflict(rows, aggregateBudget))
        return {NiaReasoningKind::Conflict, TheoryConflict{conflict->reasons}, std::nullopt};
    WorkBudget budget(262144);
    const auto propagated = LinearBoundPropagation::run(rows,
        [&](const std::string& variable, bool lower) -> std::optional<ExplainedLinearBound> {
            const auto* domain = domains.getDomain(variable);
            if (!domain || (lower ? !domain->hasLower : !domain->hasUpper)) return std::nullopt;
            const auto& bound = lower ? domain->lower : domain->upper;
            // DomainStore's empty explanations denote missing provenance,
            // not globally asserted facts as in whole-formula collection.
            if (bound.reasons.empty()) return std::nullopt;
            return ExplainedLinearBound{mpq_class(bound.value), false, bound.reasons};
        },
        [&](const std::string& variable, bool lower, const ExplainedLinearBound& bound) {
            const auto* domain = domains.getDomain(variable);
            const auto value = bound.value.get_num();
            if (domain && (lower ? domain->hasLower && domain->lower.value >= value
                                 : domain->hasUpper && domain->upper.value <= value))
                return LinearBoundUpdate::Unchanged;
            if (lower) domains.addLowerBound(variable, value, bound.reasons);
            else domains.addUpperBound(variable, value, bound.reasons);
            return domains.isEmpty(variable) ? LinearBoundUpdate::Conflict : LinearBoundUpdate::Changed;
        },
        [](const std::string&) { return true; }, budget);
    if (propagated.conflict)
        return {NiaReasoningKind::Conflict, domains.buildEmptyDomainConflict(), std::nullopt};
    updated |= propagated.updates != 0;

    if (updated) {
        return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
    }
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

} // namespace xolver
