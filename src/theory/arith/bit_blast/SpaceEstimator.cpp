#include "theory/arith/bit_blast/SpaceEstimator.h"
#include <algorithm>
#include <unordered_set>

namespace zolver::bitblast {

unsigned SpaceEstimator::bitsToCover(const mpz_class& lo, const mpz_class& hi) {
    unsigned w = 1;
    while (true) {
        mpz_class L = -(mpz_class(1) << (w - 1));
        mpz_class H =  (mpz_class(1) << (w - 1)) - 1;
        if (lo >= L && hi <= H) return w;
        ++w;
    }
}

unsigned SpaceEstimator::bitsToHold(const mpz_class& n) {
    if (n <= 1) return 1;
    unsigned w = 1;
    while ((mpz_class(1) << w) < n) ++w;   // smallest w with 2^w >= n
    return w;
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
    // Distinct graph (DG): adjacency over variables that must take different
    // values, gathered from binary `a*xi - a*xj != 0` constraints.
    std::unordered_map<std::string, std::unordered_set<std::string>> distinctAdj;
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
        // DG edge detection: a disequality whose polynomial is `a*xi - a*xj`
        // (two single-variable monomials of degree 1 with opposite coefficients,
        // no constant term) means xi != xj — exactly the pairwise atoms a k-ary
        // `distinct` lowers to.
        if (c.rel == Relation::Neq && t->size() == 2) {
            const auto& m0 = (*t)[0];
            const auto& m1 = (*t)[1];
            bool m0var = m0.powers.size() == 1 && m0.powers[0].second == 1;
            bool m1var = m1.powers.size() == 1 && m1.powers[0].second == 1;
            if (m0var && m1var && m0.coefficient == -m1.coefficient) {
                std::string a(kernel_.varName(m0.powers[0].first));
                std::string b(kernel_.varName(m1.powers[0].first));
                if (a != b) {
                    distinctAdj[a].insert(b);
                    distinctAdj[b].insert(a);
                }
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
    std::vector<std::string> unboundedVars;   // heuristic-sized; eligible for Vote
    for (const auto& v : vars) {
        const IntDomain* d = domains.getDomain(v);
        if (d && d->hasLower && d->hasUpper) {
            // Hard-bounded: width is authoritative (never touched by heuristics/Vote).
            plan.width[v] = bitsToCover(d->lower.value, d->upper.value);
            continue;
        }
        complete = false;
        unsigned cand = base;
        // Coefficient-Matching (CM), clipped to K.
        auto it = maxCoeff.find(v);
        if (it != maxCoeff.end() && it->second > 1) {
            cand = std::max(cand, std::min(bitsToHold(it->second), kCoeffClipBits));
        }
        // Distinct-Graph (DG): need enough width to hold (degree+1) distinct values.
        auto dit = distinctAdj.find(v);
        if (dit != distinctAdj.end() && !dit->second.empty()) {
            cand = std::max(cand, bitsToHold(mpz_class(dit->second.size() + 1)));
        }
        plan.width[v] = cand;
        unboundedVars.push_back(v);
    }

    // Vote (VO): if one width dominates the unbounded vars (> Gamma fraction),
    // unify them all to it (largest among the most-frequent on ties). A uniform
    // guess often lets the SAT search land directly; under-sizing an outlier is
    // safe because heuristic-mode UNSAT only triggers a refinement (never UNSAT).
    if (!unboundedVars.empty()) {
        std::unordered_map<unsigned, int> freq;
        unsigned voteBit = 0;
        int voteCnt = 0;
        for (const auto& v : unboundedVars) {
            unsigned w = plan.width[v];
            int cnt = ++freq[w];
            if (cnt > voteCnt || (cnt == voteCnt && w > voteBit)) {
                voteCnt = cnt;
                voteBit = w;
            }
        }
        if (voteCnt > static_cast<int>(kVoteThreshold *
                                       static_cast<double>(unboundedVars.size()))) {
            for (const auto& v : unboundedVars) plan.width[v] = voteBit;
        }
    }

    plan.boxIsComplete = complete && !vars.empty();
    return plan;
}

} // namespace zolver::bitblast
