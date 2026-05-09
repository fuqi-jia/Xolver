#pragma once

#include "expr/types.h"
#include "expr/ir.h"
#include "sat/SatSolver.h"
#include <vector>
#include <optional>

namespace nlcolver {

/**
 * A theory atom maps a SAT variable to a CoreIr atomic expression.
 * The expression kind is one of: Eq, Lt, Leq, Gt, Geq, Distinct.
 */
struct TheoryAtom {
    SatVar satVar;   // associated SAT literal's variable
    ExprId exprId;   // expression in CoreIr
};

/**
 * Theory conflict: a set of theory atoms that are mutually inconsistent.
 * Represented as a clause to be added to the SAT solver.
 */
struct TheoryConflict {
    std::vector<SatLit> clause; // negated theory literals
};

/**
 * Theory lemma: a valid theory consequence to be added to the SAT solver.
 * Examples: disequality split, integer branch, Gomory cut, GCD tightening.
 */
struct TheoryLemma {
    std::vector<SatLit> lits;
};

/**
 * Result of a theory check.
 */
struct TheoryCheckResult {
    enum class Kind {
        Consistent,   // assignment is theory-consistent
        Conflict,     // assignment is theory-inconsistent
        Lemma,        // theory-valid lemma to be added
        Unknown,      // solver gave up
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

/**
 * Abstract interface for theory solvers (LRA, LIA, NRA, etc.)
 */
class TheorySolver {
public:
    virtual ~TheorySolver() = default;

    virtual TheoryId id() const = 0;

    // Scope management
    virtual void push() = 0;
    virtual void pop(uint32_t n) = 0;

    // Assert a theory literal under the current SAT assignment
    virtual void assertLit(const TheoryAtom& atom, bool value, const CoreIr& ir) = 0;

    // Check theory consistency under current assertions
    virtual TheoryCheckResult check(const CoreIr& ir) = 0;

    // Reset all assertions (bounds, state, but not registered constraints)
    virtual void reset() = 0;
};

} // namespace nlcolver
