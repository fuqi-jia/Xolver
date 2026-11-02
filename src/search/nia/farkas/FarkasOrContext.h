#pragma once

#include "ir/AssertionSnapshot.h"
#include "search/nia/farkas/FarkasOrSolver.h"

namespace xolver::farkas {

// Owned by one registered reasoner. All formula-derived state is replaced
// together when its exact assertion snapshot changes, including failed search.
struct FarkasOrContext {
    AssertionSnapshot assertions;
    FarkasProfile profile;
    SupportTable table;
    bool notRefutable = false;
};

} // namespace xolver::farkas
