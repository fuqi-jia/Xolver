#pragma once

#include "expr/types.h"
#include <optional>
#include <string>
#include <vector>

namespace zolver {

struct IcpConstraint {
    std::optional<ExprId> expr; // original expression DAG (optional, for V2 backward contractors)
    PolyId poly;                // normalized p rel 0 (fallback for V1 forward eval)
    Relation rel;               // Eq, Neq, Lt, Leq, Gt, Geq
    SatLit reason;              // active literal
    TheoryId owner;             // NIA / NRA
};

struct IcpConfig {
    int maxIterations = 10000;
    int maxContractors = 100000;
    int maxSplits = 0;              // V1: only suggest, do not recursive split
    bool enableSplitSuggestion = true;
    bool enableBoundPropagationLemma = false;
    bool enableTracing = false;
};

struct SplitSuggestion {
    std::string var;
    // For NIA: split point k such that x <= k ∨ x >= k+1
    // For NRA: split point m such that x <= m ∨ x > m
    std::string splitPointDesc; // descriptive, adapter decides exact lemma
};

} // namespace zolver
