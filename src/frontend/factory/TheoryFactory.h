#pragma once

#include "expr/ir.h"
#include "theory/core/TheoryManager.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/combination/SharedTermRegistry.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/core/LogicFeatureDetector.h"
#include <memory>
#include <string>

namespace xolver {

/**
 * TheoryFactory: central factory for creating and registering concrete theory solvers.
 *
 * This is the ONLY place in the codebase that includes all concrete solver headers.
 * It isolates the rest of the frontend (including api/Solver.cpp) from solver details.
 */
struct SolverSetupResult {
    bool success = true;
    bool logicMismatch = false;
    PolynomialKernel* polyKernelRaw = nullptr;
};

SolverSetupResult setupSolvers(
    const std::string& logic,
    const LogicFeatures& features,
    CoreIr* ir,
    TheoryAtomRegistry& registry,
    TheoryManager& theoryManager,
    std::unique_ptr<SharedTermRegistry>& sharedTermRegistry,
    SortId boolSortId,
    bool liaSafeMode = false,
    bool liaUltraSafeMode = false,
    bool liaEnableSingleVar = false,
    bool liaEnableGcdIneq = false,
    bool liaEnableEqGcdNorm = false);

} // namespace xolver
