#pragma once

#include "ir/NativeTerms.h"
#include "search/coordination/TheoryManager.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "search/combination/SharedTermRegistry.h"
#include "algebra/poly/PolynomialKernel.h"
#include "contracts/LogicFeatureDetector.h"
#include "applications/smt/SolverRegistry.h"  // SolverSetupResult, BuildContext, registry
#include <memory>
#include <string>

namespace xolver {

/**
 * TheoryFactory: thin driver over SolverRegistry.
 *
 * The concrete solver headers are now included only by the builder translation
 * units that register into SolverRegistry (the builtins live in
 * TheoryFactory.cpp). setupSolvers looks up the registered builder for `logic`
 * and runs it. SolverSetupResult and BuildContext are defined in SolverRegistry.h.
 */
// Shared fallback selection for solver construction and atom registration.
// Constants still belong to arithmetic after preprocessing removes variables.
TheoryId featureArithmeticTheory(const LogicFeatures& features);

SolverSetupResult setupSolvers(
    const std::string& logic,
    const LogicFeatures& features,
    NativeTerms* ir,
    TheoryAtomRegistry& registry,
    TheoryManager& theoryManager,
    std::unique_ptr<SharedTermRegistry>& sharedTermRegistry,
    SortId boolSortId);

} // namespace xolver
