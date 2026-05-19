#pragma once

#include "expr/ir.h"
#include <gmpxx.h>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace nlcolver {

struct ArithmeticRequirement {
    bool needsNonlinearInt = false;
    bool needsEUF = false;
    bool unsupported = false;
    std::string reason;
};

struct GeneratedAssertion {
    ScopeLevel level;
    ExprId expr;
};

struct DivModOrigin {
    ExprId original;
    ExprId replacement;
    ExprId q;
    ExprId r;
    ExprId a;
    ExprId b;
};

/**
 * IntDivModLowerer: eliminates integer Kind::Div and Kind::Mod before arithmetic extraction.
 *
 * Invariants:
 *   - Pure IR-to-IR, no SAT/theory interaction.
 *   - Generated assertions carry the SAME scope level as source.
 *   - Fresh q/r scoped by (level, loweredA, loweredB), never cross-scope.
 *   - Unsupported cases set flag; caller must return Unknown without committing.
 */
class IntDivModLowerer {
public:
    explicit IntDivModLowerer(CoreIr& ir);

    // Run lowering phase. Returns true if all div/mod were lowered successfully.
    // Does NOT commit assertions — caller must validate requirement and then call commit().
    bool run();

    // Commit lowered assertions and side constraints to CoreIr.
    // Must only be called after run() succeeds and routing validation passes.
    void commit();

    bool unsupported() const { return requirement_.unsupported; }
    const std::string& unsupportedReason() const { return requirement_.reason; }
    const ArithmeticRequirement& requirement() const { return requirement_; }
    const std::vector<DivModOrigin>& origins() const { return origins_; }

private:
    ExprId lowerRec(ExprId e, ScopeLevel level);
    ExprId lowerDiv(ExprId a, ExprId b, ScopeLevel level);
    ExprId lowerMod(ExprId a, ExprId b, ScopeLevel level);
    ExprId rebuildLike(ExprId original, const std::vector<ExprId>& newChildren);

    std::optional<mpz_class> evalIntConstTerm(ExprId e) const;

    // Forward-declare nested types before use in member function signatures
    struct DivModKey;
    struct DivModKeyHash;
    struct DivModDef;

    void emitConstDivisorConstraints(const DivModDef& def, const mpz_class& k, ScopeLevel level);
    void emitVariableDivisorConstraints(const DivModDef& def, ScopeLevel level);
    void emitUndefZeroConstraints(const DivModDef& def, ScopeLevel level);

    void updateRequirement(bool needsNonlinear, bool needsEUF);

    // Check if term contains nonlinear subterms (Mul of two non-constants, Pow, etc.)
    bool containsNonlinear(ExprId e) const;

    // IR builders
    ExprId mkIntConst(int64_t v);
    ExprId mkEq(ExprId a, ExprId b);
    ExprId mkLe(ExprId a, ExprId b);
    ExprId mkLt(ExprId a, ExprId b);
    ExprId mkAdd(ExprId a, ExprId b);
    ExprId mkSub(ExprId a, ExprId b);
    ExprId mkMul(ExprId a, ExprId b);
    ExprId mkNeg(ExprId a);
    ExprId mkOr(ExprId a, ExprId b);
    ExprId mkNot(ExprId a);

    // EUF symbol management: global interned symbols, not per-run fresh.
    ExprId getOrCreateUndefDivSymbol();
    ExprId getOrCreateUndefModSymbol();
    ExprId mkUndefDivApp(ExprId a, ExprId b);
    ExprId mkUndefModApp(ExprId a, ExprId b);

private:
    CoreIr& ir_;
    SortId boolSortId_;
    SortId intSortId_;
    std::unordered_map<ExprId, ExprId> memo_;

    struct DivModKey {
        ScopeLevel level;
        ExprId a;
        ExprId b;
        bool operator==(const DivModKey& o) const noexcept {
            return level == o.level && a == o.a && b == o.b;
        }
    };
    struct DivModKeyHash {
        size_t operator()(const DivModKey& k) const noexcept {
            size_t h = std::hash<ScopeLevel>{}(k.level);
            h ^= std::hash<ExprId>{}(k.a) + 0x9e3779b97f4a7c15ULL + (h<<6) + (h>>2);
            h ^= std::hash<ExprId>{}(k.b) + 0x9e3779b97f4a7c15ULL + (h<<6) + (h>>2);
            return h;
        }
    };
    struct DivModDef {
        ExprId a = NullExpr;
        ExprId b = NullExpr;
        ExprId q = NullExpr;
        ExprId r = NullExpr;
        ExprId undefDiv = NullExpr;
        ExprId undefMod = NullExpr;
        bool arithmeticConstraintsEmitted = false;
        bool zeroBranchEmitted = false;
    };
    std::unordered_map<DivModKey, DivModDef, DivModKeyHash> registry_;

    std::vector<GeneratedAssertion> generatedAssertions_;
    std::vector<DivModOrigin> origins_;
    ArithmeticRequirement requirement_;
    ExprId undefDivSym_ = NullExpr;
    ExprId undefModSym_ = NullExpr;
    std::vector<std::pair<ScopeLevel, ExprId>> loweredAssertions_;
};

} // namespace nlcolver
