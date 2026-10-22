#pragma once

#include "algebra/linear/LinearConstraintTypes.h"
#include "algebra/poly/PolynomialKernel.h"
#include "contracts/TheorySolver.h"
#include <gmpxx.h>
#include <optional>
#include <string>
#include <vector>

namespace xolver {

// A polynomial comparison with its asserted premise. Strict relations remain
// strict over the reals; only the integer theory performs unit-gap rewriting.
struct LinearizationConstraint {
    PolyId poly;
    Relation rel;
    SatLit reason;
};

// ---------------------------------------------------------------------------
// Nonlinear term classification
// ---------------------------------------------------------------------------

// Product and square abstractions have specialized cuts. Higher powers and
// mixed monomials retain distinct keys for the full nonlinear obligation.
enum class NonlinearKind { Product, Square, Power, HigherMixed };

/**
 * NonlinearTermKey: canonical identifier for a nonlinear subterm.
 *
 * Uses sorted (varName, exponent) pairs rather than raw PolyId,
 * because PolyId is kernel-internal and may vary across reconstructions.
 */
struct NonlinearTermKey {
    NonlinearKind kind;
    std::vector<std::pair<VarId, int>> powers; // sorted by VarId

    bool operator==(const NonlinearTermKey& o) const {
        return kind == o.kind && powers == o.powers;
    }
};

struct NonlinearTermKeyHash {
    std::size_t operator()(const NonlinearTermKey& k) const {
        std::size_t h = static_cast<std::size_t>(k.kind);
        for (const auto& p : k.powers) {
            h ^= std::hash<uint32_t>{}(p.first) + 0x9e3779b9 + (h << 6) + (h >> 2);
            h ^= std::hash<int>{}(p.second) + 0x9e3779b9 + (h << 6) + (h >> 2);
        }
        return h;
    }
};

// ---------------------------------------------------------------------------
// Auxiliary variable for a nonlinear subterm
// ---------------------------------------------------------------------------

struct AuxTerm {
    std::string name;
    VarId vid = NullVar;
    PolyId poly;
    NonlinearTermKey key;
};

inline constexpr std::string_view NL_AUX_PREFIX = "__nl_aux_";
inline bool isInternalAuxVar(std::string_view name) {
    return name.size() >= NL_AUX_PREFIX.size() &&
           name.substr(0, NL_AUX_PREFIX.size()) == NL_AUX_PREFIX;
}

// ---------------------------------------------------------------------------
// Bound information with reason tracking
// ---------------------------------------------------------------------------

struct LinearizationBounds {
    mpq_class lower;
    mpq_class upper;
    std::vector<SatLit> lowerReasons;
    std::vector<SatLit> upperReasons;

    bool hasLower = false;
    bool hasUpper = false;

    bool lowerIsGlobal = false;
    bool upperIsGlobal = false;
    bool lowerReasonComplete = false;
    bool upperReasonComplete = false;

    // Strict-bound markers (NEW). `lowerStrict=true` means the constraint
    // is `x > lower` (not `x >= lower`); same for upper. Required for the
    // sign-only Family 0 cut: without these, `x > 0` would register as
    // `lower=0` and the strict-positive sign check would silently fail.
    bool lowerStrict = false;
    bool upperStrict = false;

    bool isStrictPositive() const {
        return hasLower && (lower > 0 || (lower == 0 && lowerStrict));
    }
    bool isStrictNegative() const {
        return hasUpper && (upper < 0 || (upper == 0 && upperStrict));
    }

    bool isFinite() const { return hasLower && hasUpper; }

    bool hasFiniteCompleteBounds() const {
        return isFinite() &&
               ((lowerIsGlobal || lowerReasonComplete) &&
                (upperIsGlobal || upperReasonComplete));
    }
};

// ---------------------------------------------------------------------------
// Cache key for deduplicating generated cuts
// ---------------------------------------------------------------------------

struct CutCacheKey {
    NonlinearTermKey term;
    SatLit nonlinearReason;
    std::vector<mpq_class> boundValues;
    int cutIndex;

    bool operator==(const CutCacheKey& o) const {
        return term == o.term &&
               nonlinearReason.var == o.nonlinearReason.var &&
               nonlinearReason.sign == o.nonlinearReason.sign &&
               boundValues == o.boundValues &&
               cutIndex == o.cutIndex;
    }
};

struct CutCacheKeyHash {
    std::size_t operator()(const CutCacheKey& k) const {
        std::size_t h = NonlinearTermKeyHash{}(k.term);
        h ^= std::hash<uint32_t>{}(k.nonlinearReason.var) + 0x9e3779b9 + (h << 6) + (h >> 2);
        h ^= std::hash<int>{}(k.cutIndex) + 0x9e3779b9 + (h << 6) + (h << 2);
        for (const auto& v : k.boundValues) {
            h ^= std::hash<std::string>{}(v.get_str()) + 0x9e3779b9 + (h << 6) + (h >> 2);
        }
        return h;
    }
};

// ---------------------------------------------------------------------------
// Pending lemma with optional cache metadata
// ---------------------------------------------------------------------------

struct PendingLinearizationLemma {
    TheoryLemma lemma;
    std::optional<CutCacheKey> cacheKey; // nullopt for abstraction lemmas
};

} // namespace xolver
