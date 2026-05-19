#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"
#include "theory/arith/nra/core/CdcacConstraint.h"
#include <vector>
#include <random>

namespace nlcolver {

// ------------------------------------------------------------------
// V7: Random case generators for CDCAC fuzzing
// ------------------------------------------------------------------
struct FuzzCase {
    std::vector<CdcacConstraint> constraints;
    std::vector<VarId> varOrder;
    bool expectedSat = false;
};

class CdcacFuzzer {
public:
    explicit CdcacFuzzer(uint64_t seed = 42);

    // Generate a random univariate polynomial constraint set
    FuzzCase randomUnivariate(int numConstraints, int maxDegree);

    // Generate a random bivariate constraint set
    FuzzCase randomBivariate(int numConstraints, int maxDegree);

    // Generate a case known to be SAT (simple bounds)
    FuzzCase knownSat(int numVars);

    // Generate a case known to be UNSAT (contradictory bounds)
    FuzzCase knownUnsat(int numVars);

private:
    std::mt19937_64 rng_;
};

} // namespace nlcolver
