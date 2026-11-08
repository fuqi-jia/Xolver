#pragma once

#include "contracts/TheoryAtomTypes.h"
#include <cstddef>
#include <map>
#include <span>
#include <string>
#include <utility>
#include <vector>

namespace xolver {

// Rebuild from the active trail for one check. Only indexed name pairs can
// imply an equality; unrelated shared variables need no pairwise lookup.
class LinearDifferenceEqualityIndex {
public:
    struct PinnedPair {
        size_t first;
        size_t second;
        // Bounds on the lexicographically ordered name difference. Keep both
        // reasons so callers can preserve their existing explanation order.
        SatLit lowerReason;
        SatLit upperReason;
    };

    void add(const LinearAtomPayload& atom, bool value, SatLit reason);

    // Positions refer to sharedNames, including repeated names. Results have
    // first < second and the order of an ordinary nested shared-variable loop.
    std::vector<PinnedPair> pinnedPairs(std::span<const std::string> sharedNames) const;

private:
    struct Bound {
        mpq_class coefficient;
        Relation relation;
        mpq_class rhs;
        SatLit reason;
    };
    std::map<std::pair<std::string, std::string>, std::vector<Bound>> entries_;
};

} // namespace xolver
