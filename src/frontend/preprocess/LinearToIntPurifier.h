#pragma once

#include "expr/ir.h"
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace nlcolver {

struct PurificationInfo {
    ExprId originalToInt;
    ExprId realArg;
    ExprId freshIntVar;
    ScopeLevel level;
};

struct ToIntPurifyResult {
    std::vector<std::pair<ScopeLevel, ExprId>> purifiedAssertions;
    std::vector<std::pair<ScopeLevel, ExprId>> floorLemmas;
    std::vector<PurificationInfo> infos;
    bool hasUnsupportedNonlinearToInt = false;
};

struct ToIntDetectResult {
    bool hasUnsupportedNonlinearToInt = false;
};

/**
 * LinearToIntPurifier: eliminates to_int(Real-linear-expr) by purification.
 *
 *   to_int(r)  ->  fresh Int variable k
 *   plus floor lemmas:  k <= r < k+1
 *
 * Only linear Real expressions are supported.
 * Non-linear to_int arguments are reported as unsupported.
 */
class LinearToIntPurifier {
public:
    explicit LinearToIntPurifier(CoreIr& ir) : ir_(ir) {}

    // Phase 1: detect-only.  Does NOT create fresh vars or modify IR.
    ToIntDetectResult detectOnly() const;

    // Phase 2: actual purification.  Creates fresh vars and floor lemmas.
    ToIntPurifyResult run();

private:
    CoreIr& ir_;

    struct CacheKey {
        ExprId expr;
        ScopeLevel level;
        bool operator==(const CacheKey& o) const noexcept {
            return expr == o.expr && level == o.level;
        }
    };
    struct CacheKeyHash {
        size_t operator()(const CacheKey& k) const noexcept {
            size_t h1 = std::hash<ExprId>{}(k.expr);
            size_t h2 = std::hash<ScopeLevel>{}(k.level);
            return h1 ^ (h2 + 0x9e3779b97f4a7c15ULL + (h1 << 6) + (h1 >> 2));
        }
    };

    std::unordered_map<CacheKey, ExprId, CacheKeyHash> toIntCache_;
    std::vector<PurificationInfo> infos_;
    bool hasUnsupportedNonlinearToInt_ = false;

    ExprId purifyRec(ExprId e, ScopeLevel level);
    bool isLinearRealExpr(ExprId e) const;
    bool isLinearIntExpr(ExprId e) const;
    bool isRationalConstant(ExprId e) const;
    bool isNonZeroRationalConstant(ExprId e) const;
    bool isIntegerConstant(ExprId e) const;
    bool hasUnsupportedToInt(ExprId e) const;

    ExprId makeFloorLowerLemma(ExprId k, ExprId r);
    ExprId makeFloorUpperLemma(ExprId k, ExprId r);
};

} // namespace nlcolver
