#include "theory/arith/nia/NiaLocalSearch.h"

namespace nlcolver {

NiaLocalSearch::NiaLocalSearch(PolynomialKernel& kernel) : kernel_(kernel) {}

mpz_class NiaLocalSearch::violation(
    const IntegerModel& model,
    const std::vector<NormalizedNiaConstraint>& constraints) const {

    mpz_class total = 0;
    for (const auto& c : constraints) {
        auto valOpt = kernel_.evalInteger(c.poly, model);
        if (!valOpt) continue;
        mpz_class val = *valOpt;
        mpz_class v = 0;
        switch (c.rel) {
            case Relation::Eq:  v = abs(val); break;
            case Relation::Neq: v = (val == 0) ? mpz_class(1) : mpz_class(0); break;
            case Relation::Lt:  v = (val < 0) ? mpz_class(0) : val; break;
            case Relation::Leq: v = (val <= 0) ? mpz_class(0) : val; break;
            case Relation::Gt:  v = (val > 0) ? mpz_class(0) : -val; break;
            case Relation::Geq: v = (val >= 0) ? mpz_class(0) : -val; break;
        }
        total += v * v;
    }
    return total;
}

std::optional<IntegerModel> NiaLocalSearch::tryFindModel(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const DomainStore& /*domains*/) {

    if (constraints.empty()) return IntegerModel{};

    // Collect variables
    std::unordered_set<std::string> varSet;
    for (const auto& c : constraints) {
        for (const auto& v : kernel_.variables(c.poly)) {
            varSet.insert(v);
        }
    }

    // Try a few candidate assignments
    std::vector<IntegerModel> candidates;

    // Candidate 1: all zeros
    {
        IntegerModel m;
        for (const auto& v : varSet) m[v] = 0;
        candidates.push_back(m);
    }

    // Candidate 2: small integers [-5, 5]
    // Only feasible for 1-2 variables
    if (varSet.size() <= 2) {
        std::vector<std::string> vars(varSet.begin(), varSet.end());
        if (vars.size() == 1) {
            for (int i = -5; i <= 5; ++i) {
                IntegerModel m;
                m[vars[0]] = i;
                candidates.push_back(m);
            }
        } else if (vars.size() == 2) {
            for (int i = -3; i <= 3; ++i) {
                for (int j = -3; j <= 3; ++j) {
                    IntegerModel m;
                    m[vars[0]] = i;
                    m[vars[1]] = j;
                    candidates.push_back(m);
                }
            }
        }
    }

    // Evaluate candidates
    std::optional<IntegerModel> best;
    mpz_class bestViol;
    bool first = true;

    for (const auto& m : candidates) {
        mpz_class v = violation(m, constraints);
        if (v == 0) {
            return m; // Found satisfying assignment
        }
        if (first || v < bestViol) {
            best = m;
            bestViol = v;
            first = false;
        }
    }

    // No satisfying assignment found in candidate set
    return std::nullopt;
}

} // namespace nlcolver
