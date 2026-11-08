#pragma once

#include "contracts/SatSolver.h"
#include "ir/types.h"
#include <cstdint>
#include <span>
#include <unordered_map>

namespace xolver {

class NativeTerms;

// Required halves of output <-> definition. Positive occurrences require
// output -> definition; negative occurrences require definition -> output.
struct BooleanDefinitionDirections {
    bool positive = true;
    bool negative = true;
};

using BooleanPolarities = std::unordered_map<ExprId, uint8_t>;

BooleanPolarities computeBooleanPolarities(std::span<const ExprId> roots,
                                           const NativeTerms& terms);
BooleanDefinitionDirections booleanDefinitionDirections(
    const BooleanPolarities& polarities, ExprId expression);

// Allocation and literal ownership belong to the caller. The same defining
// clauses work with every SAT backend and every theory's atomic predicates.
void emitBooleanNaryDefinition(SatSolver& solver, SatLit output,
                               std::span<const SatLit> inputs, bool conjunction,
                               BooleanDefinitionDirections directions = {});

// Full equivalence with selector-independent propagation when both branches
// agree. The caller owns allocation and any simplification or gate sharing.
void emitBooleanIteDefinition(SatSolver& solver, SatLit output,
                              SatLit selector, SatLit thenBranch, SatLit elseBranch);

} // namespace xolver
