#include "search/bitblast/SpaceEstimator.h"
#include <unordered_set>

namespace xolver::bitblast {

unsigned SpaceEstimator::bitsToCover(const mpz_class& lo, const mpz_class& hi) {
    unsigned w = 1;
    while (true) {
        mpz_class L = -(mpz_class(1) << (w - 1));
        mpz_class H =  (mpz_class(1) << (w - 1)) - 1;
        if (lo >= L && hi <= H) return w;
        ++w;
    }
}

BitWidthPlan SpaceEstimator::estimate(const std::vector<NormalizedNiaConstraint>& cs,
                                      const DomainStore& domains) const {
    BitWidthPlan plan;
    std::unordered_set<std::string> vars;
    for (const auto& c : cs)
        for (const auto& v : kernel_.variables(c.poly)) vars.insert(v);
    // Domain-only restrictions participate in encoding and completeness too.
    for (const auto& entry : domains.getAllDomains()) {
        const IntDomain& d = entry.second;
        if (d.hasLower || d.hasUpper || d.finiteValues || !d.excludedValues.empty())
            vars.insert(entry.first);
    }
    bool complete = true;
    for (const auto& v : vars) {
        const IntDomain* d = domains.getDomain(v);
        if (d && d->hasLower && d->hasUpper) {
            plan.width[v] = bitsToCover(d->lower.value, d->upper.value);
        } else {
            plan.width[v] = 2;
            complete = false;
        }
    }
    plan.boxIsComplete = complete && !vars.empty();
    return plan;
}

} // namespace xolver::bitblast
