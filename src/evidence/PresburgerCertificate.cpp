#include "evidence/PresburgerCertificate.h"

namespace xolver::proof {
namespace {
bool canonical(const std::map<VarId, mpz_class>& coefficients) {
    for (const auto& [v, a] : coefficients)
        if (v == NullVar || a == 0) return false;
    return true;
}
mpz_class coefficientGcd(const std::map<VarId, mpz_class>& coefficients) {
    mpz_class gcd = 0;
    for (const auto& [v, a] : coefficients) {
        (void)v;
        mpz_gcd(gcd.get_mpz_t(), gcd.get_mpz_t(), a.get_mpz_t());
    }
    return gcd;
}
}

bool checkIntegerLinearContradiction(const std::vector<IntegerInequality>& premises,
                                     const std::vector<mpz_class>& multipliers) {
    if (premises.size() != multipliers.size()) return false;
    std::map<VarId, mpz_class> sum;
    mpz_class bound = 0;
    for (size_t i = 0; i < premises.size(); ++i) {
        if (multipliers[i] < 0 || !canonical(premises[i].coefficients)) return false;
        for (const auto& [v, a] : premises[i].coefficients) sum[v] += multipliers[i] * a;
        bound += multipliers[i] * premises[i].bound;
    }
    for (const auto& [v, a] : sum) {
        (void)v;
        if (a != 0) return false;
    }
    return bound < 0;
}

bool checkIntegerGcdTightening(const IntegerInequality& premise,
                               const IntegerInequality& conclusion) {
    if (!canonical(premise.coefficients) || !canonical(conclusion.coefficients)) return false;
    mpz_class gcd = coefficientGcd(premise.coefficients);
    if (gcd == 0 || premise.coefficients.size() != conclusion.coefficients.size()) return false;
    for (const auto& [v, a] : premise.coefficients) {
        auto it = conclusion.coefficients.find(v);
        if (it == conclusion.coefficients.end() || a != gcd * it->second) return false;
    }
    mpz_class bound;
    mpz_fdiv_q(bound.get_mpz_t(), premise.bound.get_mpz_t(), gcd.get_mpz_t());
    return conclusion.bound == bound;
}

bool checkIntegerEqualityContradiction(const std::map<VarId, mpz_class>& coefficients,
                                       const mpz_class& rhs) {
    if (!canonical(coefficients)) return false;
    mpz_class gcd = coefficientGcd(coefficients);
    if (gcd == 0) return rhs != 0;
    return !mpz_divisible_p(rhs.get_mpz_t(), gcd.get_mpz_t());
}

} // namespace xolver::proof
