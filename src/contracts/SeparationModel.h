#pragma once
#include "xolver/SeparationLogic.h"
#include "xolver/Model.h"
#include "contracts/PresburgerFormula.h"
#include <set>

namespace xolver::sl {
struct ArithmeticInterpretation {
    pa::ModelEvidence evidence;
    std::map<Location, std::string> integers;
    std::map<Location, std::string> predicates;
    std::set<std::string> publicSymbols;
};
// Evidence and exported interpretation travel with the ordinary query model.
// Invalidating that model also invalidates its heap; there is no separate cache.
struct Interpretation {
    Formula query;
    Model abstract;
    HeapModel heap;
    std::map<Location, std::string> literals;
    std::map<std::string, Location> bindings;
    std::set<std::string> booleans;
    std::map<std::string, std::string> assignments;
    std::map<uint64_t, std::string> values;
    std::optional<ArithmeticInterpretation> arithmetic;
};
// Check the spatial formula AND the concrete integer renaming, including nil,
// literal anchors, stack assignments and every heap cell.
Evaluation checkInterpretation(const Interpretation&, Limits = {});
} // namespace xolver::sl
