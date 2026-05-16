#include "theory/arith/nia/LinearNiaDomainReasoner.h"

namespace nlcolver {

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

    if (updated) {
        return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
    }
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

} // namespace nlcolver
