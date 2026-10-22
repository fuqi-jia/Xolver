#pragma once

#include "ir/types.h"
#include <optional>

namespace xolver {

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
};

} // namespace xolver
