#pragma once

#include "expr/types.h"
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

using TheoryAtomPayload = std::variant<
    LinearAtomPayload,
    PolynomialAtomPayload
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

struct TheoryConflict {
    std::vector<SatLit> clause;
};

struct TheoryLemma {
    std::vector<SatLit> lits;
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
    virtual void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) = 0;

    // Backtrack to target decision level
    virtual void backtrackToLevel(int level) = 0;

    // Check current incremental state
    virtual TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb) = 0;

    // Reset ONCE per fresh check-sat initialization
    virtual void reset() = 0;
};

// Legacy struct (for backward compatibility during transition)
struct TheoryAtom {
    SatVar satVar;
    ExprId exprId;
};

} // namespace nlcolver
