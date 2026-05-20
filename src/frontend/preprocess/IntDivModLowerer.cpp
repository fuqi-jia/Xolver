#include "frontend/preprocess/IntDivModLowerer.h"
#include <cassert>
#include <iostream>

namespace nlcolver {

IntDivModLowerer::IntDivModLowerer(CoreIr& ir)
    : ir_(ir), boolSortId_(ir.boolSortId()), intSortId_(ir.intSortId()) {
}

bool IntDivModLowerer::run() {
    requirement_ = {};
    generatedAssertions_.clear();
    origins_.clear();
    registry_.clear();
    memo_.clear();
    loweredAssertions_.clear();

    auto scoped = ir_.getScopedAssertions();
    std::vector<std::pair<ScopeLevel, ExprId>> loweredScoped;

    for (const auto& [level, a] : scoped) {
        memo_.clear();
        ExprId lowered = lowerRec(a, level);
        if (requirement_.unsupported) {
            return false;
        }
        loweredScoped.push_back({level, lowered});
    }

    for (const auto& gen : generatedAssertions_) {
        loweredScoped.push_back({gen.level, gen.expr});
    }

    loweredAssertions_ = std::move(loweredScoped);
    return true;
}

void IntDivModLowerer::commit() {
    ir_.clearAssertions();
    for (const auto& [level, e] : loweredAssertions_) {
        ir_.addAssertion(e, level);
    }
}

ExprId IntDivModLowerer::lowerRec(ExprId e, ScopeLevel level) {
    if (auto it = memo_.find(e); it != memo_.end()) {
        return it->second;
    }

    // Copy node because recursive lowerRec() and rebuildLike() may call
    // ir_.add(), which can reallocate the internal exprs_ vector and
    // invalidate references.
    const auto node = ir_.get(e);

    // Rebuild children first (post-order)
    std::vector<ExprId> newChildren;
    newChildren.reserve(node.children.size());
    bool changed = false;
    for (ExprId c : node.children) {
        ExprId lc = lowerRec(c, level);
        if (lc != c) changed = true;
        newChildren.push_back(lc);
    }

    ExprId rebuilt = changed ? rebuildLike(e, newChildren) : e;

    // Handle div/mod
    if (node.kind == Kind::Div && node.sort == intSortId_) {
        assert(newChildren.size() == 2);
        // Div lowering
        ExprId result = lowerDiv(newChildren[0], newChildren[1], level);
        memo_[e] = result;
        return result;
    }

    if (node.kind == Kind::Mod && node.sort == intSortId_) {
        assert(newChildren.size() == 2);
        // Mod lowering
        ExprId result = lowerMod(newChildren[0], newChildren[1], level);
        memo_[e] = result;
        return result;
    }

    if (node.kind == Kind::Ite) {
        // ITE should have been eliminated by CoreIteLowerer
        std::cerr << "[IntDivModLowerer] ERROR: Kind::Ite not lowered before div/mod lowering\n";
        assert(false && "ITE should be eliminated before IntDivModLowerer");
    }

    memo_[e] = rebuilt;
    return rebuilt;
}

ExprId IntDivModLowerer::lowerDiv(ExprId a, ExprId b, ScopeLevel level) {
    lowerMod(a, b, level);  // ensure def exists and constraints are emitted
    DivModKey key{level, a, b};
    auto it = registry_.find(key);
    assert(it != registry_.end());
    return it->second.q;
}

ExprId IntDivModLowerer::lowerMod(ExprId a, ExprId b, ScopeLevel level) {
    DivModKey key{level, a, b};
    auto it = registry_.find(key);
    if (it == registry_.end()) {
        DivModDef def;
        def.a = a;
        def.b = b;
        def.q = ir_.makeFreshVariable(intSortId_, "__nlc_div_q");
        def.r = ir_.makeFreshVariable(intSortId_, "__nlc_mod_r");
        auto [insertedIt, _] = registry_.emplace(key, def);
        it = insertedIt;
    }
    DivModDef& def = it->second;

    auto optK = evalIntConstTerm(b);
    if (optK) {
        const mpz_class& k = *optK;
        // const divisor
        if (k == 0) {
            if (!def.zeroBranchEmitted) {
                emitUndefZeroConstraints(def, level);
                def.zeroBranchEmitted = true;
            }
        } else {
            if (!def.arithmeticConstraintsEmitted) {
                emitConstDivisorConstraints(def, k, level);
                def.arithmeticConstraintsEmitted = true;
            }
        }
    } else {
        // variable divisor
        // Variable divisor
        if (!def.arithmeticConstraintsEmitted && !def.zeroBranchEmitted) {
            emitVariableDivisorConstraints(def, level);
            def.arithmeticConstraintsEmitted = true;
            def.zeroBranchEmitted = true;
        }
    }

    origins_.push_back({/*original=*/ExprId{}, /*replacement=*/def.r, def.q, def.r, a, b});

    return def.r;
}

ExprId IntDivModLowerer::rebuildLike(ExprId original, const std::vector<ExprId>& newChildren) {
    const auto& node = ir_.get(original);
    bool changed = false;
    for (size_t i = 0; i < newChildren.size(); ++i) {
        if (newChildren[i] != node.children[i]) {
            changed = true;
            break;
        }
    }
    if (!changed) return original;

    CoreExpr ne;
    ne.kind = node.kind;
    ne.sort = node.sort;
    for (ExprId c : newChildren) ne.children.push_back(c);
    ne.payload = node.payload;
    return ir_.add(std::move(ne));
}

std::optional<mpz_class> IntDivModLowerer::evalIntConstTerm(ExprId e) const {
    const auto& node = ir_.get(e);
    switch (node.kind) {
    case Kind::ConstInt:
        if (auto* v = std::get_if<int64_t>(&node.payload.value)) {
            return mpz_class(*v);
        }
        return std::nullopt;
    case Kind::ConstReal:
        // Defensive: SOMTParser currently maps integer literals to ConstReal
        // with Real sort in some contexts. We accept them here only when the
        // denominator is 1 (i.e. the value is mathematically an integer).
        // This is safe because IntDivModLowerer only operates on Int-sort
        // subexpressions, so any ConstReal encountered here is semantically
        // an integer constant that leaked through the parser.
        if (auto* s = std::get_if<std::string>(&node.payload.value)) {
            mpq_class q(*s);
            if (q.get_den() == 1) {
                return mpz_class(q.get_num());
            }
        }
        return std::nullopt;
    case Kind::Neg:
        if (node.children.size() == 1) {
            if (auto v = evalIntConstTerm(node.children[0])) {
                return -(*v);
            }
        }
        return std::nullopt;
    case Kind::Add:
        if (node.children.size() == 2) {
            if (auto a = evalIntConstTerm(node.children[0]);
                auto b = evalIntConstTerm(node.children[1])) {
                return *a + *b;
            }
        }
        return std::nullopt;
    case Kind::Sub:
        if (node.children.size() == 2) {
            if (auto a = evalIntConstTerm(node.children[0]);
                auto b = evalIntConstTerm(node.children[1])) {
                return *a - *b;
            }
        }
        return std::nullopt;
    case Kind::Mul:
        if (node.children.size() == 2) {
            if (auto a = evalIntConstTerm(node.children[0]);
                auto b = evalIntConstTerm(node.children[1])) {
                return *a * *b;
            }
        }
        return std::nullopt;
    default:
        return std::nullopt;
    }
}

bool IntDivModLowerer::containsNonlinear(ExprId e) const {
    const auto& node = ir_.get(e);
    switch (node.kind) {
    case Kind::Mul:
        if (node.children.size() == 2) {
            bool leftConst = evalIntConstTerm(node.children[0]).has_value();
            bool rightConst = evalIntConstTerm(node.children[1]).has_value();
            if (!leftConst && !rightConst) return true;
        }
        break;
    case Kind::Pow:
        return true;
    case Kind::Div:
    case Kind::Mod:
        // These should not appear (they are being lowered), but mark nonlinear if they do
        return true;
    default:
        break;
    }
    // Recurse into children
    for (ExprId c : node.children) {
        if (containsNonlinear(c)) return true;
    }
    return false;
}

void IntDivModLowerer::emitConstDivisorConstraints(const DivModDef& def, const mpz_class& k, ScopeLevel level) {
    ExprId kExpr = mkIntConst(k.get_si());
    mpz_class absKMinusOneVal = abs(k);
    absKMinusOneVal -= 1;
    ExprId absKMinusOne = mkIntConst(absKMinusOneVal.get_si());

    // a = k*q + r
    generatedAssertions_.push_back({level, mkEq(def.a, mkAdd(mkMul(kExpr, def.q), def.r))});
    // 0 <= r
    generatedAssertions_.push_back({level, mkLe(mkIntConst(0), def.r)});
    // r <= abs(k)-1
    generatedAssertions_.push_back({level, mkLe(def.r, absKMinusOne)});

    bool nonlinear = containsNonlinear(def.a);
    updateRequirement(nonlinear, false);
}

void IntDivModLowerer::emitVariableDivisorConstraints(const DivModDef& def, ScopeLevel level) {
    ExprId zero = mkIntConst(0);
    ExprId one = mkIntConst(1);

    ExprId bEqZero = mkEq(def.b, zero);
    ExprId bGtZero = mkLt(zero, def.b);
    ExprId bLtZero = mkLt(def.b, zero);

    // a = b*q + r (shared equation)
    ExprId equation = mkEq(def.a, mkAdd(mkMul(def.b, def.q), def.r));

    // b = 0 => q = __undef_div(a,b), r = __undef_mod(a,b)
    ExprId qUndef = mkEq(def.q, mkUndefDivApp(def.a, def.b));
    ExprId rUndef = mkEq(def.r, mkUndefModApp(def.a, def.b));
    generatedAssertions_.push_back({level, mkOr(mkNot(bEqZero), qUndef)});
    generatedAssertions_.push_back({level, mkOr(mkNot(bEqZero), rUndef)});

    // b > 0 => a = b*q + r, 0 <= r, r <= b - 1
    generatedAssertions_.push_back({level, mkOr(mkNot(bGtZero), equation)});
    generatedAssertions_.push_back({level, mkOr(mkNot(bGtZero), mkLe(zero, def.r))});
    generatedAssertions_.push_back({level, mkOr(mkNot(bGtZero), mkLe(def.r, mkSub(def.b, one)))});

    // b < 0 => a = b*q + r, 0 <= r, r <= -b - 1
    generatedAssertions_.push_back({level, mkOr(mkNot(bLtZero), equation)});
    generatedAssertions_.push_back({level, mkOr(mkNot(bLtZero), mkLe(zero, def.r))});
    generatedAssertions_.push_back({level, mkOr(mkNot(bLtZero), mkLe(def.r, mkSub(mkNeg(def.b), one)))});

    updateRequirement(true, true);
}

void IntDivModLowerer::emitUndefZeroConstraints(const DivModDef& def, ScopeLevel level) {
    ExprId qUndef = mkEq(def.q, mkUndefDivApp(def.a, def.b));
    ExprId rUndef = mkEq(def.r, mkUndefModApp(def.a, def.b));
    generatedAssertions_.push_back({level, qUndef});
    generatedAssertions_.push_back({level, rUndef});
    updateRequirement(false, true);
}

void IntDivModLowerer::updateRequirement(bool needsNonlinear, bool needsEUF) {
    if (needsNonlinear) requirement_.needsNonlinearInt = true;
    if (needsEUF) requirement_.needsEUF = true;
}

// ---------------------------------------------------------------------------
// IR builders
// ---------------------------------------------------------------------------

ExprId IntDivModLowerer::mkIntConst(int64_t v) {
    CoreExpr e;
    e.kind = Kind::ConstInt;
    e.sort = intSortId_;
    e.payload = Payload(v);
    return ir_.add(std::move(e));
}

ExprId IntDivModLowerer::mkEq(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Eq;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId IntDivModLowerer::mkLe(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Leq;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId IntDivModLowerer::mkLt(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Lt;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId IntDivModLowerer::mkAdd(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Add;
    e.sort = intSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId IntDivModLowerer::mkSub(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Sub;
    e.sort = intSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId IntDivModLowerer::mkMul(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Mul;
    e.sort = intSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId IntDivModLowerer::mkNeg(ExprId a) {
    CoreExpr e;
    e.kind = Kind::Neg;
    e.sort = intSortId_;
    e.children.push_back(a);
    return ir_.add(std::move(e));
}

ExprId IntDivModLowerer::mkOr(ExprId a, ExprId b) {
    CoreExpr e;
    e.kind = Kind::Or;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.add(std::move(e));
}

ExprId IntDivModLowerer::mkNot(ExprId a) {
    CoreExpr e;
    e.kind = Kind::Not;
    e.sort = boolSortId_;
    e.children.push_back(a);
    return ir_.add(std::move(e));
}

// ---------------------------------------------------------------------------
// EUF symbol management
// ---------------------------------------------------------------------------

ExprId IntDivModLowerer::getOrCreateUndefDivSymbol() {
    if (undefDivSym_ != NullExpr) return undefDivSym_;
    // Create a placeholder Variable node to serve as the UF symbol name carrier.
    // In NLColver's IR, UF symbols are represented by Variable nodes with special names.
    CoreExpr e;
    e.kind = Kind::Variable;
    e.sort = intSortId_;
    e.payload = Payload(std::string("__undef_div"));
    undefDivSym_ = ir_.add(std::move(e));
    return undefDivSym_;
}

ExprId IntDivModLowerer::getOrCreateUndefModSymbol() {
    if (undefModSym_ != NullExpr) return undefModSym_;
    CoreExpr e;
    e.kind = Kind::Variable;
    e.sort = intSortId_;
    e.payload = Payload(std::string("__undef_mod"));
    undefModSym_ = ir_.add(std::move(e));
    return undefModSym_;
}

ExprId IntDivModLowerer::mkUndefDivApp(ExprId a, ExprId b) {
    ExprId sym = getOrCreateUndefDivSymbol();
    CoreExpr e;
    e.kind = Kind::UFApply;
    e.sort = intSortId_;
    e.children.push_back(sym);
    e.children.push_back(a);
    e.children.push_back(b);
    e.payload = Payload(std::string("__undef_div"));
    return ir_.add(std::move(e));
}

ExprId IntDivModLowerer::mkUndefModApp(ExprId a, ExprId b) {
    ExprId sym = getOrCreateUndefModSymbol();
    CoreExpr e;
    e.kind = Kind::UFApply;
    e.sort = intSortId_;
    e.children.push_back(sym);
    e.children.push_back(a);
    e.children.push_back(b);
    e.payload = Payload(std::string("__undef_mod"));
    return ir_.add(std::move(e));
}

} // namespace nlcolver
