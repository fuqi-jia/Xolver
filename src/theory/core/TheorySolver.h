#pragma once

#include "theory/core/TheoryAtomTypes.h"
#include "util/RealValue.h"
#include <vector>
#include <optional>
#include <unordered_map>

namespace zolver {

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
    // Active linear context for nonlinear solvers (optional; default = no-op)
    // -----------------------------------------------------------------------
    virtual void setActiveLinearContext(const std::vector<ActiveLinearConstraint>* context) {
        (void)context;
    }

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
        // variable name -> value string (e.g. "x" -> "42", "y" -> "3/4").
        // Legacy channel; carries both numeric and boolean values as strings.
        std::unordered_map<std::string, std::string> assignments;
        // Typed numeric channel (RealValue unification, Phase 1). Solvers that
        // have migrated populate this; consumers prefer it for arithmetic
        // variables and fall back to `assignments` otherwise. Lets NRA export
        // exact algebraic models (e.g. √2) instead of a lossy string.
        std::unordered_map<std::string, RealValue> numericAssignments;

        // Interpretation of an uninterpreted function symbol as a finite
        // table plus a default. Each entry maps a concrete argument tuple to
        // a value; arguments not in the table take `deflt`. Populated by the
        // validated candidate search for QF_UF* model output (get-model).
        struct FuncEntry {
            std::vector<std::string> args;  // one value string per argument
            std::string value;
        };
        struct FuncInterp {
            std::vector<std::string> argSorts;  // "Int"/"Real"/"Bool" per arg
            std::string retSort;
            std::vector<FuncEntry> entries;
            std::string deflt;                  // value for unlisted tuples
        };
        std::unordered_map<std::string, FuncInterp> functionInterps;

        // Interpretation of an array variable: a default element plus a finite
        // set of (index, element) overrides. Equal arrays share one interp.
        // `defaultVal` is the value at any index not listed in `entries`.
        // Index/element values are opaque tokens that compare by equality
        // (e.g. eclass-rep markers like "@arr_e7"), since QF_AX indices and
        // elements may be uninterpreted-sort. Populated by EufSolver::getModel.
        struct ArrayInterp {
            std::string indexSort;
            std::string elemSort;
            std::string defaultVal;
            std::vector<std::pair<std::string, std::string>> entries; // (index, value)
        };
        std::unordered_map<std::string, ArrayInterp> arrayInterps;
    };
    virtual std::optional<TheoryModel>
    getModel() const { return std::nullopt; }
};

// Legacy struct (for backward compatibility during transition)
struct TheoryAtom {
    SatVar satVar;
    ExprId exprId;
};

} // namespace zolver
