#pragma once

#include "expr/ir.h"
#include <unordered_map>
#include <string>
#include <functional>

namespace xolver {

/**
 * Local Search Advisor: proposes candidate models for MCSAT / NIA.
 *
 * Stage G skeleton:
 *   - Cost function over boolean + theory assignments
 *   - Move generator (flip bool, nudge real/int value)
 *   - Restart policy (geometric, Luby)
 */
class LocalSearchAdvisor {
public:
    struct ModelProposal {
        std::unordered_map<std::string, double> realValues;
        std::unordered_map<std::string, bool> boolValues;
        double cost;
    };

    // Initialize with current SAT + theory state.
    void init(const CoreIr& ir);

    // Generate next proposal.
    ModelProposal propose();

    // Accept/reject feedback.
    void feedback(bool accepted, double cost);

    // Restart.
    void restart();

private:
    // TODO: cost function, move generator, tabu list, restart policy
};

} // namespace xolver
