#include "theory/arith/nia/core/LinearNiaDomainReasoner.h"

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

    // Second pass: propagate bounds through binary equalities like x - y = 0
    for (const auto& c : constraints) {
        if (c.rel != Relation::Eq) continue;
        auto termsOpt = kernel_.terms(c.poly);
        if (!termsOpt) continue;
        const auto& terms = *termsOpt;

        const PolynomialKernel::MonomialTerm* constTerm = nullptr;
        std::vector<const PolynomialKernel::MonomialTerm*> varTerms;
        for (const auto& t : terms) {
            if (t.powers.empty()) {
                constTerm = &t;
            } else if (t.powers.size() == 1 && t.powers[0].second == 1) {
                varTerms.push_back(&t);
            } else {
                varTerms.clear();
                break;
            }
        }
        if (varTerms.size() != 2) continue;
        if (constTerm && constTerm->coefficient != 0) continue;

        const auto& t1 = *varTerms[0];
        const auto& t2 = *varTerms[1];
        if (t1.coefficient != -t2.coefficient) continue;

        std::string var1 = std::string(kernel_.varName(t1.powers[0].first));
        std::string var2 = std::string(kernel_.varName(t2.powers[0].first));

        const IntDomain* d1 = domains.getDomain(var1);
        const IntDomain* d2 = domains.getDomain(var2);
        if (!d1 && !d2) continue;

        auto propagate = [&](const std::string& srcVar, const std::string& dstVar,
                             const IntDomain* srcDomain) {
            if (!srcDomain) return false;
            bool changed = false;
            if (srcDomain->hasLower) {
                domains.addLowerBound(dstVar, srcDomain->lower.value, c.reason);
                changed = true;
            }
            if (srcDomain->hasUpper) {
                domains.addUpperBound(dstVar, srcDomain->upper.value, c.reason);
                changed = true;
            }
            return changed;
        };

        if (d1 && !d2) {
            if (propagate(var1, var2, d1)) updated = true;
        } else if (!d1 && d2) {
            if (propagate(var2, var1, d2)) updated = true;
        } else if (d1 && d2) {
            // Both have bounds: tighten each with the other's bounds
            if (d1->hasLower && (!d2->hasLower || d1->lower.value > d2->lower.value)) {
                domains.addLowerBound(var2, d1->lower.value, c.reason);
                updated = true;
            }
            if (d1->hasUpper && (!d2->hasUpper || d1->upper.value < d2->upper.value)) {
                domains.addUpperBound(var2, d1->upper.value, c.reason);
                updated = true;
            }
            if (d2->hasLower && (!d1->hasLower || d2->lower.value > d1->lower.value)) {
                domains.addLowerBound(var1, d2->lower.value, c.reason);
                updated = true;
            }
            if (d2->hasUpper && (!d1->hasUpper || d2->upper.value < d1->upper.value)) {
                domains.addUpperBound(var1, d2->upper.value, c.reason);
                updated = true;
            }
        }
    }

    if (updated) {
        return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
    }
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

} // namespace nlcolver
