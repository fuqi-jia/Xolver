#pragma once
#include "xolver/SeparationLogic.h"

namespace xolver::sl {
// Bind a conflict claim to the two original locations whose equality is
// forbidden. Search may use this to construct a path; replay validates it.
std::optional<std::pair<Location, Location>>
conflictEndpoints(const SymbolicHeap&, const Conflict&);
}
