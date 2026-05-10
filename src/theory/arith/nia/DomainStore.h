#pragma once

#include "theory/TheorySolver.h"
#include <gmpxx.h>
#include <string>
#include <vector>
#include <set>
#include <map>
#include <optional>
#include <unordered_set>

namespace nlcolver {

// Note: using std::string directly for NIA variable names
// (expr/types.h defines VarId as uint32_t, which is different)

struct BoundWithReason {
    mpz_class value;
    std::vector<SatLit> reasons;
};

struct IntDomain {
    bool hasLower = false;
    bool hasUpper = false;
    BoundWithReason lower;
    BoundWithReason upper;

    std::optional<std::set<mpz_class>> finiteValues;
    std::vector<SatLit> finiteSetReasons;
    std::map<mpz_class, std::vector<SatLit>> excludedValues;
};

/**
 * DomainStore: maintains per-variable integer domains.
 *
 * Supports intervals, finite sets, and exclusions. All updates carry reasons.
 * Can detect empty domains and build sound conflicts.
 */
class DomainStore {
public:
    void reset();

    void restrictToFiniteSet(const std::string& var, const std::set<mpz_class>& values, SatLit reason);
    void addLowerBound(const std::string& var, const mpz_class& lb, SatLit reason);
    void addUpperBound(const std::string& var, const mpz_class& ub, SatLit reason);
    void excludeValue(const std::string& var, const mpz_class& v, SatLit reason);

    bool isEmpty(const std::string& var) const;
    bool isEmpty() const;

    bool allFinite(const std::unordered_set<std::string>& vars) const;
    mpz_class totalSize(const std::unordered_set<std::string>& vars) const;

    const IntDomain* getDomain(const std::string& var) const;

    TheoryConflict buildEmptyDomainConflict() const;

private:
    std::map<std::string, IntDomain> domains_;

    bool isDomainEmpty(const IntDomain& d) const;
    std::vector<SatLit> collectEmptyReasons(const IntDomain& d) const;
};

} // namespace nlcolver
