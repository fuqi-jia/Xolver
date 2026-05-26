#pragma once

#include "expr/types.h"
#include "expr/ir.h"
#include "sat/SatSolver.h"
#include "theory/core/LinearFormKey.h"
#include "util/RealValue.h"
#include <vector>
#include <optional>
#include <variant>
#include <gmpxx.h>

namespace zolver {

// Forward declaration
class TheoryLemmaDatabase;

// ---------------------------------------------------------------------------
// EufAtomKind & EufAtomPayload (moved from EufTypes.h to break dependency)
// ---------------------------------------------------------------------------
enum class EufAtomKind : uint8_t {
    Equality,
    Disequality,
    BoolTermAsFormula
};

struct EufAtomPayload {
    ExprId lhs;
    ExprId rhs;
    Relation rel;
    EufAtomKind kind = EufAtomKind::Equality;
};

// ---------------------------------------------------------------------------
// Theory atom payloads
// ---------------------------------------------------------------------------

struct LinearAtomPayload {
    LinearFormKey lhs;
    Relation rel;
    RealValue rhs;
};

struct PolynomialAtomPayload {
    PolyId poly;
    Relation rel;
    RealValue rhs;
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

// Semantic class of a lemma (master guardrail: tag by semantics, not theory).
//   Entailment: an unconditional logical consequence (e.g. an LRA Farkas
//               row-propagation reasons ⟹ impliedBound) — a theory tautology,
//               sound to give the SAT solver in ANY branch.
//   Guess:      a branch/case-split lemma (e.g. an NIA partial-assignment
//               branch) that may prune valid models — only sound at a full
//               model check, NOT during search.
enum class LemmaKind : uint8_t { Guess, Entailment };

// TheoryLemma stores a propagation lemma in the form:
//   (¬reason₁ ∨ ¬reason₂ ∨ ... ∨ implied)
// where each literal is expressed in its SAT-polarity form.
struct TheoryLemma {
    std::vector<SatLit> lits;
    LemmaKind kind = LemmaKind::Guess;  // conservative default
};

/**
 * ActiveLinearConstraint: a linear constraint that is true under the
 * current SAT assignment.  Used by NiraSolver to obtain linear context
 * without reading coreIr_->assertions() directly.
 */
struct ActiveLinearConstraint {
    SatLit reasonLit;
    LinearAtomPayload payload;
};

enum class TheoryEffort : uint8_t {
    Standard,
    Full
};

// ---------------------------------------------------------------------------
// Theory clause normalization
// ---------------------------------------------------------------------------
// Sorts, deduplicates exact literals, and detects complementary pairs.
// Returns false if a complementary pair is found (indicates a bug in conflict
// construction).  Modifies the vector in-place.
// ---------------------------------------------------------------------------
inline bool normalizeTheoryClause(std::vector<SatLit>& lits) {
    std::sort(lits.begin(), lits.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    lits.erase(std::unique(lits.begin(), lits.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), lits.end());
    for (size_t i = 0; i < lits.size(); ++i) {
        SatLit neg = lits[i].negated();
        auto it = std::lower_bound(lits.begin(), lits.end(), neg, [](SatLit a, SatLit b) {
            if (a.var != b.var) return a.var < b.var;
            return a.sign < b.sign;
        });
        if (it != lits.end() && *it == neg) {
            return false; // complementary pair detected
        }
    }
    return true;
}

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
    std::string reason; // human-readable for Unknown; optional for others

    static TheoryCheckResult consistent() {
        return {Kind::Consistent, std::nullopt, std::nullopt, {}};
    }
    static TheoryCheckResult mkConflict(TheoryConflict c) {
        return {Kind::Conflict, std::move(c), std::nullopt, {}};
    }
    static TheoryCheckResult mkLemma(TheoryLemma l) {
        return {Kind::Lemma, std::nullopt, std::move(l), {}};
    }
    static TheoryCheckResult unknown(std::string reason = {}) {
        return {Kind::Unknown, std::nullopt, std::nullopt, std::move(reason)};
    }
};

} // namespace zolver
