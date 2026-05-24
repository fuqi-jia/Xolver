#pragma once

#include "expr/ir.h"
#include <unordered_map>
#include <vector>

namespace nlcolver {

/**
 * ToIntDefinitionalLowerer (Capability 8c of the close-all-known-fails plan).
 *
 * Replaces LinearToIntPurifier. Lowers every Kind::ToInt (and Kind::IsInt)
 * occurrence into a definitional triple:
 *
 *   (to_int t)   -->   i_t   (fresh Int variable)
 *   with side constraints:
 *     (= r_t t)                       ; r_t fresh Real, equality routed to LRA/NRA
 *     (<= (to_real i_t) r_t)
 *     (<  r_t (+ (to_real i_t) 1))
 *
 *   (is_int t)   -->   (= r_t (to_real i_t))
 *
 * Unlike LinearToIntPurifier this pass succeeds on NONLINEAR `t`. The bridge
 * equality `r_t = t` is forwarded to whichever theory owns `t` (LRA for
 * linear-real, NRA for nonlinear-real, LIRA/NIRA for mixed). The Solver is
 * responsible for upgrading the declared logic if the introduced bridge
 * raises the theory level (e.g. QF_LIRA -> QF_NIRA).
 *
 * Soundness: the SMT-LIB semantics of `to_int(t) = i` is `i <= t < i + 1`
 * with `i` integer. The bridge equality `r_t = t` is equisatisfiable: r_t is
 * fresh and only constrained by these atoms, so every model of the original
 * assignment extends to a model of the lowered formula and vice versa.
 *
 * Reports `hadNonlinearBridge()` true iff any introduced bridge equality
 * `r_t = t` has a nonlinear `t`. Reports `hadIntBridge()` true iff any
 * introduced bridge equality refers to Int-sorted variables (so a pure-Real
 * logic must upgrade to a mixed-sort logic).
 */
class ToIntDefinitionalLowerer {
public:
    explicit ToIntDefinitionalLowerer(CoreIr& ir);

    bool run();
    void commit();

    bool hadNonlinearBridge() const { return hadNonlinearBridge_; }
    bool hadIntBridge() const { return hadIntBridge_; }
    bool hadRealBridge() const { return hadRealBridge_; }
    bool didLower() const { return didLower_; }

private:
    ExprId rewriteRec(ExprId e, ScopeLevel level);
    ExprId getOrLowerToInt(ExprId arg, ScopeLevel level);

    // IR builders.
    ExprId mkConstInt(int64_t v);
    ExprId mkConstReal(const std::string& s);
    ExprId mkToReal(ExprId child);
    ExprId mkLeq(ExprId a, ExprId b);
    ExprId mkLt(ExprId a, ExprId b);
    ExprId mkEq(ExprId a, ExprId b);
    ExprId mkAdd(ExprId a, ExprId b);

    bool isNonlinearReal(ExprId e) const;
    bool refersToIntVar(ExprId e) const;
    bool refersToRealVar(ExprId e) const;

    CoreIr& ir_;
    SortId boolSortId_;
    SortId intSortId_;
    SortId realSortId_;

    // (Real-coerced arg ExprId, scope) -> i_t  : memoize lowering so repeated
    // occurrences of (to_int t) for the same t reuse the same i_t.
    struct Key {
        ExprId arg;
        ScopeLevel level;
        bool operator==(const Key& o) const noexcept {
            return arg == o.arg && level == o.level;
        }
    };
    struct KeyHash {
        size_t operator()(const Key& k) const noexcept {
            size_t h = std::hash<ExprId>{}(k.arg);
            h ^= std::hash<ScopeLevel>{}(k.level) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
            return h;
        }
    };
    std::unordered_map<Key, ExprId, KeyHash> toIntCache_;
    std::unordered_map<ExprId, ExprId> rewriteMemo_;
    std::vector<std::pair<ScopeLevel, ExprId>> lowered_;
    std::vector<std::pair<ScopeLevel, ExprId>> sideAssertions_;

    bool hadNonlinearBridge_ = false;
    bool hadIntBridge_ = false;
    bool hadRealBridge_ = false;
    bool didLower_ = false;
};

} // namespace nlcolver
