#pragma once

#include "theory/core/TheoryAtomTypes.h"
#include <vector>
#include <optional>
#include <unordered_map>

namespace nlcolver {

class TheoryLemmaStorage;

// ---------------------------------------------------------------------------
// Abstract interface for theory solvers
// ---------------------------------------------------------------------------

class TheorySolver {
public:
    virtual ~TheorySolver() = default;

    virtual TheoryId id() const = 0;

    // Scope management (for Solver::push/pop API)
    virtual void push() = 0;
    virtual void pop(uint32_t n) = 0;

    // Incremental assertion from SAT trail
    virtual void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) = 0;

    // Backtrack to target decision level
    virtual void backtrackToLevel(int level) = 0;

    // Check current incremental state
    virtual TheoryCheckResult check(TheoryLemmaStorage& lemmaDb,
                                    TheoryEffort effort = TheoryEffort::Standard) = 0;

    // Reset ONCE per fresh check-sat initialization
    virtual void reset() = 0;

    // -----------------------------------------------------------------------
    // Nelson-Oppen combination hooks (optional; default = no-op)
    // -----------------------------------------------------------------------
    virtual bool supportsCombination() const { return false; }

    virtual TheoryCheckResult assertInterfaceEquality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) {
        (void)a; (void)b; (void)reason; (void)level;
        return TheoryCheckResult::consistent();
    }

    virtual TheoryCheckResult assertInterfaceDisequality(
        SharedTermId a, SharedTermId b, SatLit reason, int level) {
        (void)a; (void)b; (void)reason; (void)level;
        return TheoryCheckResult::consistent();
    }

    struct SharedEqualityPropagation {
        SharedTermId a;
        SharedTermId b;
        std::vector<SatLit> reasons;
    };

    virtual std::vector<SharedEqualityPropagation>
    getDeducedSharedEqualities() { return {}; }

    struct TheoryModel {
        // variable name -> value string (e.g. "x" -> "42", "y" -> "3/4")
        std::unordered_map<std::string, std::string> assignments;
    };
    virtual std::optional<TheoryModel>
    getModel() const { return std::nullopt; }
};

// Legacy struct (for backward compatibility during transition)
struct TheoryAtom {
    SatVar satVar;
    ExprId exprId;
};

} // namespace nlcolver
