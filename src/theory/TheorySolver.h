#pragma once

#include "expr/types.h"
#include "theory/euf/EufTypes.h"
#include "expr/ir.h"
#include "sat/SatSolver.h"
#include "theory/arith/linear/LinearExpr.h"
#include <vector>
#include <optional>
#include <variant>
#include <gmpxx.h>

namespace nlcolver {

// Forward declaration
class TheoryLemmaDatabase;

// ---------------------------------------------------------------------------
// Theory atom payloads
// ---------------------------------------------------------------------------

struct LinearAtomPayload {
    LinearFormKey lhs;
    Relation rel;
    mpq_class rhs;
};

struct PolynomialAtomPayload {
    PolyId poly;
    Relation rel;
    mpq_class rhs;
};

struct SharedEqualityPayload {
    SharedTermId a;
    SharedTermId b;
};

using TheoryAtomPayload = std::variant<
    LinearAtomPayload,
    PolynomialAtomPayload,
    EufAtomPayload,
    SharedEqualityPayload
>;

// ---------------------------------------------------------------------------
// TheoryAtomRecord: maps a SAT variable to its theory semantics.
// ---------------------------------------------------------------------------

struct TheoryAtomRecord {
    SatVar satVar;
    TheoryId theory;
    bool isDynamic;
    ExprId exprId;  // diagnostic only; routing uses satVar
    TheoryAtomPayload payload;
};

// ---------------------------------------------------------------------------
// Theory conflict / lemma / check result
// ---------------------------------------------------------------------------

// TheoryConflict stores raw reason literals: each literal is TRUE in the
// current SAT assignment (it is the reason why the corresponding bound/
// equality was asserted).  It is the caller's responsibility (typically
// TheoryManager) to negate each literal before submitting the clause as a
// falsified external conflict to the SAT solver.
struct TheoryConflict {
    std::vector<SatLit> clause;
};

// TheoryLemma stores a propagation lemma in the form:
//   (¬reason₁ ∨ ¬reason₂ ∨ ... ∨ implied)
// where each literal is expressed in its SAT-polarity form.
struct TheoryLemma {
    std::vector<SatLit> lits;
};

enum class TheoryEffort : uint8_t {
    Standard,
    Full
};

struct TheoryCheckResult {
    enum class Kind {
        Consistent,
        Conflict,
        Lemma,
        Unknown,
    };

    Kind kind;
    std::optional<TheoryConflict> conflictOpt;
    std::optional<TheoryLemma> lemmaOpt;

    static TheoryCheckResult consistent() {
        return {Kind::Consistent, std::nullopt, std::nullopt};
    }
    static TheoryCheckResult mkConflict(TheoryConflict c) {
        return {Kind::Conflict, std::move(c), std::nullopt};
    }
    static TheoryCheckResult mkLemma(TheoryLemma l) {
        return {Kind::Lemma, std::nullopt, std::move(l)};
    }
    static TheoryCheckResult unknown() {
        return {Kind::Unknown, std::nullopt, std::nullopt};
    }
};

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
    virtual TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb,
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
