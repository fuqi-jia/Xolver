#pragma once

#include <cstddef>

namespace xolver {

class SatSolver;
class TheoryAtomRegistry;

// Compile exact relations between predicates of one linear expression into
// Boolean propagation. Ordered cuts need O(n) clauses after O(n log n) sorting;
// equality and disequality use their two registered arithmetic endpoints.
class BoundAxiomGenerator {
public:
    static std::size_t generate(TheoryAtomRegistry& registry, SatSolver& sat);
};

} // namespace xolver
