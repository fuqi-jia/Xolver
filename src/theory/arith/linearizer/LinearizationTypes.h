#pragma once

#include "theory/arith/linear/LinearConstraintTypes.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/core/TheorySolver.h"
#include <gmpxx.h>
#include <optional>
#include <string>
#include <vector>

namespace xolver {

// ---------------------------------------------------------------------------
// Nonlinear term classification
// ---------------------------------------------------------------------------

// MGC-RD Phase 2A: extended to recognize higher-degree and mixed monomials.
// Product/Square stay as before for back-compat with McCormick/SquareCut paths.
// Power (NEW): single variable x^N with N >= 3. Replaces HigherMixed routing
//   for the single-variable case so it can get a proper convex-envelope cut
//   (Phase 1 PowerCutGenerator), not just a sign lemma.
// HigherMixed catches truly multi-variable monomials (x*y*z, theta*vv1*vv3^2)
//   that the legacy detector rejected silently. The abstraction emits a
//   sign-based bound cut when factor signs are determined, giving the SAT
//   layer SOMETHING to branch on.
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

struct BoundInfo {
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
