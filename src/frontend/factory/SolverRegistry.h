#pragma once

// Logic-builder registry — the contract the frontend uses to register and look up
// the per-logic theory-solver stack builders. It references only the IR foundation
// (expr/ir.h) and forward-declares everything else, so it stays cheap to include and
// the IR layering holds (narrowness enforced by tools/governance/check_architecture.sh).

#include "expr/ir.h"  // CoreIr, SortId, ExprId — the IR foundation

#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <vector>

namespace xolver {

// Forward declarations — the builder translation units include the real headers;
// this header stays free of solver/engine internals.
struct LogicFeatures;
class TheoryAtomRegistry;
class TheoryManager;
class SharedTermRegistry;
class PolynomialKernel;

// The five LIA knobs threaded from the CLI / set-option.
struct LiaConfig {
    bool safeMode = false;
    bool ultraSafeMode = false;
    bool enableSingleVar = false;
    bool enableGcdIneq = false;
    bool enableEqGcdNorm = false;
};

// Outcome of a build attempt.
struct SolverSetupResult {
    bool success = true;
    bool logicMismatch = false;
    PolynomialKernel* polyKernelRaw = nullptr;
};

// Everything a builder needs to construct and wire a theory-solver stack. Passed
// by reference; a builder mutates *theoryManager / *sharedTermRegistry / *result.
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
    // Register a builder for one or more logics (priority 0 = builtin); a later,
    // strictly higher-priority registration shadows an earlier one for the same name.
    static void registerLogic(std::vector<std::string> logics, int priority,
                              LogicBuilder builder, const char* label = "");

    static const LogicBuilder* builderFor(const std::string& logic);
    static std::size_t size();

    // Idempotently register the builtin builders (the builder translation units
    // register at static init); this guarantees the builtins are present.
    static void ensureBuiltinsRegistered();
};

} // namespace xolver
