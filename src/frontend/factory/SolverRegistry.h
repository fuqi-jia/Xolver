#pragma once

#include "expr/ir.h"
#include "theory/core/LogicFeatureDetector.h"
#include <functional>
#include <memory>
#include <string>
#include <vector>

// SolverRegistry: the registration seam that replaces TheoryFactory's hardcoded
// logic→solver-stack dispatch. Each logic family registers a *builder* that
// constructs and wires its theory-solver stack into the TheoryManager. The open
// core registers its builtins; closed-source "pro" stacks/engines self-register
// the same way from src/pro/ — so adding a pro logic or engine never edits this
// file. This header is deliberately free of concrete-solver headers (it is the
// stable seam); the builders that reference LraSolver/NraSolver/... live in the
// .cpp translation units that register them.

namespace xolver {

class TheoryAtomRegistry;
class TheoryManager;
class SharedTermRegistry;
class PolynomialKernel;

// The five LIA knobs threaded from the CLI / set-option, bundled so builders
// don't each take them as positional args.
struct LiaConfig {
    bool safeMode = false;
    bool ultraSafeMode = false;
    bool enableSingleVar = false;
    bool enableGcdIneq = false;
    bool enableEqGcdNorm = false;
};

// Outcome of a build attempt (mirrors the legacy SolverSetupResult).
struct SolverSetupResult {
    bool success = true;
    bool logicMismatch = false;
    PolynomialKernel* polyKernelRaw = nullptr;
};

// Everything a builder needs to construct and wire a stack. Passed by reference;
// builders mutate theoryManager / sharedTermRegistry / result.
struct BuildContext {
    std::string logic;
    const LogicFeatures& features;
    CoreIr* ir = nullptr;
    TheoryAtomRegistry* registry = nullptr;
    TheoryManager* theoryManager = nullptr;
    std::unique_ptr<SharedTermRegistry>* sharedTermRegistry = nullptr;
    SortId boolSortId{};
    LiaConfig lia;
    SolverSetupResult* result = nullptr;
};

using LogicBuilder = std::function<void(BuildContext&)>;

class SolverRegistry {
public:
    // Register `builder` for every name in `logics`. A later registration with a
    // strictly higher priority overrides an earlier one for the same name (so a
    // pro stack can shadow an open-core default). Priority 0 = open-core builtin.
    static void registerLogic(std::vector<std::string> logics, int priority,
                              LogicBuilder builder, const char* label = "");

    // Highest-priority builder registered for `logic`, or nullptr if none.
    static const LogicBuilder* builderFor(const std::string& logic);

    // Test/introspection: number of distinct logic names registered.
    static std::size_t size();

    // Idempotently register the open-core builtin logic builders. Called once at
    // the start of setupSolvers; pro builders self-register via static init.
    static void ensureBuiltinsRegistered();
};

} // namespace xolver
