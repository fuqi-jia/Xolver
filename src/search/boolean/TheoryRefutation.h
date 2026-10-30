#pragma once

#include "contracts/SatSolver.h"
#include <functional>
#include <optional>
#include <span>

namespace xolver {

struct BooleanRefutationLimits {
    size_t assignments = 8;
    int satConflicts = 1000;
    std::chrono::steady_clock::time_point deadline =
        std::chrono::steady_clock::time_point::max();
};

struct BooleanRefutationResult {
    bool refuted = false;
    size_t assignments = 0;
    size_t conflicts = 0;
    bool exhausted = false;
};

// Select a sufficient set of true atom literals from the current Boolean model.
// The oracle may refute any subset, returning its true premise literals. It must
// justify that conflict in its theory; absence of a conflict is never SAT.
using RefutationAssignment = std::function<std::vector<SatLit>(const SatSolver&)>;
using TheoryRefutationOracle =
    std::function<std::optional<std::vector<SatLit>>(std::span<const SatLit>)>;

// Bounded Boolean/theory refutation, independent of any particular theory.
// The caller supplies an already encoded Boolean abstraction and exact theory
// explanations. Unsupported/invalid explanations leave the obligation open.
BooleanRefutationResult refuteBooleanTheory(
    SatSolver&, const RefutationAssignment&, const TheoryRefutationOracle&,
    const BooleanRefutationLimits&);

} // namespace xolver
