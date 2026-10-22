#pragma once

#include <compare>
#include <cstdint>
#include <gmpxx.h>
#include <map>
#include <variant>
#include <vector>

namespace xolver::proof {

// Locations have identity, not integer arithmetic. This prevents the pure
// Presburger solver from accidentally imposing integer semantics on addresses.
struct HeapLocation {
    uint64_t id;
    auto operator<=>(const HeapLocation&) const = default;
};
using HeapValue = std::variant<HeapLocation, mpz_class>;
using HeapRecord = std::vector<HeapValue>;
using FiniteHeap = std::map<HeapLocation, HeapRecord>;
struct GroundPointsTo {
    HeapLocation address;
    HeapRecord record;
};

// Concrete witness for a separating conjunction of points-to atoms (empty
// vector means emp). Exact heap semantics: no extra cells, no overlap, and nil
// cannot be allocated. Pure formulas and quantifiers are separate obligations.
bool checkGroundSymbolicHeap(const FiniteHeap& model,
                             const std::vector<GroundPointsTo>& atoms,
                             HeapLocation nil = {0});

// A concrete star witness: the pairwise disjoint parts have exactly the whole
// heap as their union. Neither bounded search nor failure to find a partition
// is an UNSAT proof.
bool checkHeapPartition(const FiniteHeap& whole,
                         const std::vector<FiniteHeap>& parts,
                         HeapLocation nil = {0});

} // namespace xolver::proof
