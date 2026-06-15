#pragma once

// Xolver Solver SPI (Service Provider Interface) — the STABLE, VERSIONED contract
// a closed-source "pro" module builds against to register additional theory-solver
// stacks/engines, without editing any open-core file. This is the only header pro
// links against for registration. It deliberately references only the IR
// foundation (expr/ir.h) and forward-declares everything else; it must NOT pull in
// concrete solver/engine headers (enforced by scripts/check_architecture.sh) so the
// contract stays narrow and the open core stays decoupled from pro.
//
// Versioning: a pro module is compiled with this header's XOLVER_SPI_VERSION baked
// in and passes it to registerProLogic(); the core compares it against its own and
// REJECTS a major mismatch, so a pro plugin built against an incompatible SPI can
// never silently register a broken builder. Bump XOLVER_SPI_VERSION only on a
// breaking change to BuildContext / the registration signature.

#include "expr/ir.h"  // CoreIr, SortId, ExprId — the IR foundation (allowed in spi/)

#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <vector>

#define XOLVER_SPI_VERSION 1

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

    // Versioned pro entrypoint. `proSpiVersion` is the pro module's compiled-in
    // XOLVER_SPI_VERSION; the core (which owns this definition) compares it against
    // its own and refuses to register on a major mismatch, returning false. Pro
    // code must call THIS, never registerLogic directly.
    static bool registerProLogic(int proSpiVersion, std::vector<std::string> logics,
                                 int priority, LogicBuilder builder,
                                 const char* label = "");

    // The core library's compiled-in SPI version (for diagnostics / handshake).
    static int coreSpiVersion();

    static const LogicBuilder* builderFor(const std::string& logic);
    static std::size_t size();

    // Idempotently register the open-core builtin builders. Pro builders
    // self-register via static init; this just guarantees the builtins are present.
    static void ensureBuiltinsRegistered();
};

} // namespace xolver
