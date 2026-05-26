#include "theory/arith/bit_blast/SpaceEstimator.h"
#include <algorithm>
#include <unordered_set>

namespace nlcolver::bitblast {

unsigned SpaceEstimator::bitsToCover(const mpz_class& lo, const mpz_class& hi) {
    unsigned w = 1;
    while (true) {
        mpz_class L = -(mpz_class(1) << (w - 1));
        mpz_class H =  (mpz_class(1) << (w - 1)) - 1;
        if (lo >= L && hi <= H) return w;
        ++w;
    }
}

BitWidthPlan SpaceEstimator::grow(BitWidthPlan plan, unsigned maxBW) {
    for (auto& kv : plan.width) kv.second = std::min(maxBW, kv.second * 2);
    return plan;
}

BitWidthPlan SpaceEstimator::estimate(const std::vector<NormalizedNiaConstraint>& cs,
                                      const DomainStore& domains) const {
    BitWidthPlan plan;
    std::unordered_set<std::string> vars;
    std::unordered_map<std::string, mpz_class> maxCoeff;
    unsigned mulCount = 0;

    for (const auto& c : cs) {
        auto t = kernel_.terms(c.poly);
        if (!t) {
            for (const auto& v : kernel_.variables(c.poly)) vars.insert(v);
            continue;
        }
        for (const auto& m : *t) {
            int deg = 0;
            for (const auto& pe : m.powers) deg += pe.second;
            if (deg >= 2) ++mulCount;
            for (const auto& pe : m.powers) {
                std::string n(kernel_.varName(pe.first));
                vars.insert(n);
                mpz_class ac = abs(m.coefficient);
                auto it = maxCoeff.find(n);
                if (it == maxCoeff.end() || ac > it->second) maxCoeff[n] = ac;
            }
        }
    }

    // Also include variables that appear ONLY in DomainStore restrictions (not
    // in any cs polynomial). They must be encoded and validated too, otherwise a
    // domain-only inconsistency (e.g. an empty domain on z) could be missed and
    // we'd return a spurious SAT. This makes the search self-contained.
    for (const auto& entry : domains.getAllDomains()) {
        const IntDomain& d = entry.second;
        bool restricted = d.hasLower || d.hasUpper || d.finiteValues || !d.excludedValues.empty();
        if (restricted) vars.insert(entry.first);
    }

    // Multiplication-Adaptation: shrink the heuristic base as products multiply.
    unsigned base = (mulCount > 64) ? 3u : (mulCount > 16 ? 4u : 6u);

    bool complete = true;
    for (const auto& v : vars) {
        const IntDomain* d = domains.getDomain(v);
        if (d && d->hasLower && d->hasUpper) {
            plan.width[v] = bitsToCover(d->lower.value, d->upper.value);
        } else {
            complete = false;
            unsigned cand = base;
            auto it = maxCoeff.find(v);
            if (it != maxCoeff.end() && it->second > 0) {
                unsigned cb = static_cast<unsigned>(
                    mpz_sizeinbase(it->second.get_mpz_t(), 2)) + 1;
                cand = std::max(cand, std::min(cb, 16u));   // Coefficient-Matching, capped K=16
            }
            plan.width[v] = cand;
        }
    }

    plan.boxIsComplete = complete && !vars.empty();
    return plan;
}

} // namespace nlcolver::bitblast
