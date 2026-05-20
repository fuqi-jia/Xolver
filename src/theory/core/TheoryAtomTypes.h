#pragma once

#include "expr/types.h"
#include "expr/ir.h"
#include "sat/SatSolver.h"
#include "theory/core/LinearFormKey.h"
#include <vector>
#include <optional>
#include <variant>
#include <gmpxx.h>

namespace nlcolver {

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

} // namespace nlcolver
