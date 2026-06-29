#pragma once

// Internal logic-builder registry — the contract the frontend uses to register and
// look up the per-logic theory-solver stack builders. It deliberately references
// only the IR foundation (expr/ir.h) and forward-declares everything else; it must
// NOT pull in concrete solver/engine headers (enforced by
// tools/governance/check_architecture.sh) so the header stays narrow and the IR
// layering holds.

#include "expr/ir.h"  // CoreIr, SortId, ExprId — the IR foundation

#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <vector>

namespace xolver {

// Forward declarations — pro implementations include the real headers; the SPI
// surface itself stays free of solver/engine internals.
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
    // Open-core registration (priority 0 = builtin). A later registration with a
    // strictly higher priority shadows an earlier one for the same logic name.
    static void registerLogic(std::vector<std::string> logics, int priority,
                              LogicBuilder builder, const char* label = "");

    static const LogicBuilder* builderFor(const std::string& logic);
    static std::size_t size();

    // Idempotently register the open-core builtin builders. Pro builders
    // self-register via static init; this just guarantees the builtins are present.
    static void ensureBuiltinsRegistered();
};

} // namespace xolver
