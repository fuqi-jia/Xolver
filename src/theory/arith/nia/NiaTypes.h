#pragma once

#include "theory/core/TheorySolver.h"
#include <optional>

namespace nlcolver {

// Forward declaration from NiaSolver
struct ActiveNiaConstraint;

// Common result type for all NIA reasoning engines
enum class NiaReasoningKind {
    NoChange,      // not applicable / incomplete / skipped, continue
    DomainUpdated, // domains modified, continue to next engine
    Conflict,      // sound UNSAT proof found
    Lemma,         // theory lemma generated
    FatalUnknown   // fatal unsupported state, must terminate
};

struct NiaReasoningResult {
    NiaReasoningKind kind;
    std::optional<TheoryConflict> conflict;
    std::optional<TheoryLemma> lemma;
};

} // namespace nlcolver
