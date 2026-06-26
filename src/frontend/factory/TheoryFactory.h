#pragma once

#include "expr/ir.h"
#include "theory/core/TheoryManager.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/combination/SharedTermRegistry.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "theory/core/LogicFeatureDetector.h"
#include "frontend/factory/SolverRegistry.h"  // SolverSetupResult, BuildContext, registry
#include <memory>
#include <string>

namespace xolver {

/**
 * TheoryFactory: thin driver over SolverRegistry.
 *
 * The concrete solver headers are now included only by the builder translation
 * units that register into SolverRegistry (the open-core builtins live in
 * TheoryFactory.cpp; pro stacks self-register from src/pro/). setupSolvers looks
 * up the registered builder for `logic` and runs it; the legacy signature is
 * kept so api/Solver.cpp is unchanged. `SolverSetupResult` is defined in
 * SolverRegistry.h.
 */
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
