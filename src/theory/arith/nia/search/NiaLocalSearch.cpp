#include "theory/arith/nia/search/NiaLocalSearch.h"
#include <random>
#include <algorithm>
#include <functional>

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
    const DomainStore& domains) {

    if (constraints.empty()) return IntegerModel{};

    // Collect variables in deterministic order
    std::vector<std::string> vars;
    for (const auto& c : constraints) {
        for (const auto& v : kernel_.variables(c.poly)) {
            if (std::find(vars.begin(), vars.end(), v) == vars.end()) {
                vars.push_back(v);
            }
        }
    }

    std::vector<IntegerModel> candidates;

    // Candidate 1: all zeros
    {
        IntegerModel m;
        for (const auto& v : vars) m[v] = 0;
        candidates.push_back(m);
    }

    // Candidate 2: domain bounds and midpoints
    for (const auto& v : vars) {
        const auto* d = domains.getDomain(v);
        if (d && d->hasLower && d->hasUpper) {
            mpz_class lb = d->lower.value;
            mpz_class ub = d->upper.value;
            mpz_class mid = (lb + ub) / 2;
            for (const auto& val : {lb, ub, mid}) {
                IntegerModel m;
                for (const auto& vv : vars) m[vv] = 0;
                m[v] = val;
                candidates.push_back(m);
            }
        }
    }

    // Candidate 3: enumerate small finite domains
    bool allFinite = true;
    mpz_class totalSize = 1;
    for (const auto& v : vars) {
        const auto* d = domains.getDomain(v);
        if (!d || !d->hasLower || !d->hasUpper) {
            allFinite = false;
            break;
        }
        mpz_class sz = d->upper.value - d->lower.value + 1;
        if (sz <= 0) {
            allFinite = false;
            break;
        }
        totalSize *= sz;
        if (totalSize > 200) {
            allFinite = false;
            break;
        }
    }

    if (allFinite && totalSize <= 200) {
        // Full enumeration for tiny domains
        auto enumerate = [&](auto&& self, size_t idx, IntegerModel& cur) -> void {
            if (idx == vars.size()) {
                candidates.push_back(cur);
                return;
            }
            const auto* d = domains.getDomain(vars[idx]);
            mpz_class lb = d->lower.value;
            mpz_class ub = d->upper.value;
            for (mpz_class val = lb; val <= ub; ++val) {
                cur[vars[idx]] = val;
                self(self, idx + 1, cur);
            }
        };
        IntegerModel cur;
        for (const auto& v : vars) cur[v] = 0;
        enumerate(enumerate, 0, cur);
    } else {
        // Candidate 4: small integers [-5, 5] for few variables
        if (vars.size() <= 2) {
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

        // Candidate 5: deterministic sampling across domain
        for (int s = 0; s < 20; ++s) {
            IntegerModel m;
            for (const auto& v : vars) {
                const auto* d = domains.getDomain(v);
                if (d && d->hasLower && d->hasUpper) {
                    mpz_class lb = d->lower.value;
                    mpz_class ub = d->upper.value;
                    mpz_class range = ub - lb;
                    if (range > 0) {
                        mpz_class step = range / 20 + 1;
                        m[v] = lb + step * s;
                        if (m[v] > ub) m[v] = ub;
                    } else {
                        m[v] = lb;
                    }
                } else {
                    m[v] = s - 10;
                }
            }
            candidates.push_back(m);
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

    // Hill-climbing local search from the best candidate
    if (best) {
        IntegerModel cur = *best;
        mpz_class curViol = bestViol;
        const int MAX_STEPS = 100;
        for (int step = 0; step < MAX_STEPS; ++step) {
            bool improved = false;
            for (const auto& v : vars) {
                for (int delta : {-1, 1}) {
                    IntegerModel next = cur;
                    next[v] += delta;
                    // Respect domain bounds if available
                    const auto* d = domains.getDomain(v);
                    if (d && d->hasLower && next[v] < d->lower.value) continue;
                    if (d && d->hasUpper && next[v] > d->upper.value) continue;

                    mpz_class vNext = violation(next, constraints);
                    if (vNext == 0) {
                        return next;
                    }
                    if (vNext <= curViol) {
                        cur = next;
                        curViol = vNext;
                        improved = true;
                        break; // accept first improving or equal move
                    }
                }
                if (improved) break;
            }
            if (!improved) break; // local minimum
        }
    }

    // No satisfying assignment found
    return std::nullopt;
}

} // namespace nlcolver
