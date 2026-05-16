#include "theory/arith/nia/DomainStore.h"
#include <algorithm>

namespace nlcolver {

void DomainStore::reset() {
    domains_.clear();
}

void DomainStore::restrictToFiniteSet(const std::string& var,
                                      const std::set<mpz_class>& values,
                                      SatLit reason) {
    IntDomain& d = domains_[var];
    d.finiteSetReasons.push_back(reason);
    if (!d.finiteValues) {
        d.finiteValues = values;
    } else {
        std::set<mpz_class> intersection;
        std::set_intersection(d.finiteValues->begin(), d.finiteValues->end(),
                              values.begin(), values.end(),
                              std::inserter(intersection, intersection.begin()));
        *d.finiteValues = std::move(intersection);
    }
}

void DomainStore::addLowerBound(const std::string& var, const mpz_class& lb, SatLit reason) {
    IntDomain& d = domains_[var];
    if (!d.hasLower || lb > d.lower.value) {
        d.lower.value = lb;
        d.lower.reasons.clear();
        d.lower.reasons.push_back(reason);
        d.hasLower = true;
    } else if (lb == d.lower.value) {
        d.lower.reasons.push_back(reason);
    }
}

void DomainStore::addUpperBound(const std::string& var, const mpz_class& ub, SatLit reason) {
    IntDomain& d = domains_[var];
    if (!d.hasUpper || ub < d.upper.value) {
        d.upper.value = ub;
        d.upper.reasons.clear();
        d.upper.reasons.push_back(reason);
        d.hasUpper = true;
    } else if (ub == d.upper.value) {
        d.upper.reasons.push_back(reason);
    }
}

void DomainStore::excludeValue(const std::string& var, const mpz_class& v, SatLit reason) {
    IntDomain& d = domains_[var];
    d.excludedValues[v].push_back(reason);
}

bool DomainStore::isDomainEmpty(const IntDomain& d) const {
    // Check bounds conflict
    if (d.hasLower && d.hasUpper && d.lower.value > d.upper.value) {
        return true;
    }
    // Check finite set empty
    if (d.finiteValues && d.finiteValues->empty()) {
        return true;
    }
    // Check finite set disjoint from bounds and exclusions
    if (d.finiteValues) {
        bool anyValid = false;
        for (const auto& v : *d.finiteValues) {
            if (d.hasLower && v < d.lower.value) continue;
            if (d.hasUpper && v > d.upper.value) continue;
            if (d.excludedValues.count(v)) continue;
            anyValid = true;
            break;
        }
        if (!anyValid) return true;
    } else {
        // No finite set; check if all values in [lb, ub] are excluded
        if (d.hasLower && d.hasUpper) {
            bool allExcluded = true;
            for (mpz_class v = d.lower.value; v <= d.upper.value; ++v) {
                if (!d.excludedValues.count(v)) {
                    allExcluded = false;
                    break;
                }
            }
            if (allExcluded) return true;
        }
    }
    return false;
}

bool DomainStore::isEmpty(const std::string& var) const {
    auto it = domains_.find(var);
    if (it == domains_.end()) return false;
    return isDomainEmpty(it->second);
}

bool DomainStore::isEmpty() const {
    for (const auto& [var, d] : domains_) {
        if (isDomainEmpty(d)) return true;
    }
    return false;
}

bool DomainStore::allFinite(const std::unordered_set<std::string>& vars) const {
    for (const auto& var : vars) {
        auto it = domains_.find(var);
        if (it == domains_.end()) return false;
        const IntDomain& d = it->second;
        if (!d.finiteValues || d.finiteValues->empty()) {
            if (!d.hasLower || !d.hasUpper) return false;
        }
    }
    return true;
}

mpz_class DomainStore::totalSize(const std::unordered_set<std::string>& vars) const {
    mpz_class total = 1;
    for (const auto& var : vars) {
        auto it = domains_.find(var);
        if (it == domains_.end()) return mpz_class(0);
        const IntDomain& d = it->second;
        if (d.finiteValues && !d.finiteValues->empty()) {
            mpz_class count = 0;
            for (const auto& v : *d.finiteValues) {
                if (d.hasLower && v < d.lower.value) continue;
                if (d.hasUpper && v > d.upper.value) continue;
                if (d.excludedValues.count(v)) continue;
                ++count;
            }
            total *= count;
        } else if (d.hasLower && d.hasUpper) {
            mpz_class lb = d.lower.value;
            mpz_class ub = d.upper.value;
            mpz_class excludedInRange = 0;
            for (const auto& [val, _] : d.excludedValues) {
                if (val >= lb && val <= ub) ++excludedInRange;
            }
            mpz_class rangeSize = ub - lb + 1;
            if (rangeSize < 0) rangeSize = 0;
            total *= (rangeSize - excludedInRange);
        } else {
            return mpz_class(0);
        }
    }
    return total;
}

const IntDomain* DomainStore::getDomain(const std::string& var) const {
    auto it = domains_.find(var);
    if (it == domains_.end()) return nullptr;
    return &it->second;
}

std::vector<SatLit> DomainStore::collectEmptyReasons(const IntDomain& d) const {
    std::vector<SatLit> reasons;
    auto add = [&reasons](const std::vector<SatLit>& rs) {
        reasons.insert(reasons.end(), rs.begin(), rs.end());
    };

    // Bounds conflict
    if (d.hasLower && d.hasUpper && d.lower.value > d.upper.value) {
        add(d.lower.reasons);
        add(d.upper.reasons);
        return reasons;
    }

    // Finite set empty after intersection
    if (d.finiteValues && d.finiteValues->empty()) {
        add(d.finiteSetReasons);
        return reasons;
    }

    // Finite set disjoint from bounds
    if (d.finiteValues) {
        bool disjoint = true;
        for (const auto& v : *d.finiteValues) {
            if (d.hasLower && v < d.lower.value) continue;
            if (d.hasUpper && v > d.upper.value) continue;
            if (d.excludedValues.count(v)) continue;
            disjoint = false;
            break;
        }
        if (disjoint) {
            add(d.lower.reasons);
            add(d.upper.reasons);
            add(d.finiteSetReasons);
            return reasons;
        }
    }

    // All values in [lb, ub] excluded
    if (d.hasLower && d.hasUpper) {
        bool allExcluded = true;
        for (mpz_class v = d.lower.value; v <= d.upper.value; ++v) {
            if (!d.excludedValues.count(v)) {
                allExcluded = false;
                break;
            }
        }
        if (allExcluded) {
            add(d.lower.reasons);
            add(d.upper.reasons);
            for (const auto& [val, rs] : d.excludedValues) {
                add(rs);
            }
            return reasons;
        }
    }

    return reasons;
}

TheoryConflict DomainStore::buildEmptyDomainConflict() const {
    std::vector<SatLit> clause;
    for (const auto& [var, d] : domains_) {
        if (isDomainEmpty(d)) {
            auto reasons = collectEmptyReasons(d);
            clause.insert(clause.end(), reasons.begin(), reasons.end());
            break; // Only report first empty domain
        }
    }
    // Negate all reasons
    // Reasons are already in true-under-model form; do not negate here.
    // TheoryManager will negate them into a conflict clause.
    return TheoryConflict{clause};
}

} // namespace nlcolver
