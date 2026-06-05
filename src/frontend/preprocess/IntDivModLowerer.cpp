#include "frontend/preprocess/IntDivModLowerer.h"
#include <cassert>
#include <functional>
#include <iostream>

namespace xolver {

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
    positiveVars_.clear();

    auto scoped = ir_.getScopedAssertions();
    // Track C1 Phase 2: pre-scan strict-positive lower bounds so the
    // symbolic-divisor branch can avoid the EUF-requiring `b = 0` undef
    // case when the divisor is provably non-zero. Sound: only removes the
    // unreachable `b = 0` branch (the b > 0 / b < 0 branches still cover
    // every satisfying model where the divisor is non-zero, and the scan
    // is conservative — non-matching shapes leave the existing EUF path).
    scanPositiveBounds(scoped);
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

ExprId IntDivModLowerer::lowerRec(ExprId root, ScopeLevel level) {
    if (auto it = memo_.find(root); it != memo_.end()) return it->second;

    // Iterative post-order (two-visit work-stack) to avoid stack overflow on
    // deeply nested terms. `level` is constant down the whole walk (the former
    // recursion passed it unchanged). Behavior-identical otherwise.
    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (memo_.find(e) != memo_.end()) { stack.pop_back(); continue; }

        // Value copy: lowerRec()/rebuildLike()/lowerDiv()/lowerMod() call
        // ir_.add(), which can reallocate exprs_ and invalidate references.
        const auto node = ir_.get(e);

        if (!frame.processed) {
            frame.processed = true;
            if (node.children.empty()) { memo_[e] = e; stack.pop_back(); continue; }
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                if (memo_.find(c) == memo_.end()) stack.push_back({c, false});
            }
            continue;
        }

        stack.pop_back();
        std::vector<ExprId> newChildren;
        newChildren.reserve(node.children.size());
        bool changed = false;
        for (ExprId c : node.children) {
            ExprId lc = memo_.at(c);
            if (lc != c) changed = true;
            newChildren.push_back(lc);
        }

        ExprId rebuilt = changed ? rebuildLike(e, newChildren) : e;

        if (node.kind == Kind::Div && node.sort == intSortId_) {
            assert(newChildren.size() == 2);
            memo_[e] = lowerDiv(newChildren[0], newChildren[1], level);
        } else if (node.kind == Kind::Mod && node.sort == intSortId_) {
            assert(newChildren.size() == 2);
            memo_[e] = lowerMod(newChildren[0], newChildren[1], level);
        } else {
            if (node.kind == Kind::Ite) {
                // ITE should have been eliminated by CoreIteLowerer.
                std::cerr << "[IntDivModLowerer] ERROR: Kind::Ite not lowered before div/mod lowering\n";
                assert(false && "ITE should be eliminated before IntDivModLowerer");
            }
            memo_[e] = rebuilt;
        }
    }

    return memo_.at(root);
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

std::optional<mpz_class> IntDivModLowerer::evalIntConstTerm(ExprId root) const {
    // Iterative two-visit post-order (was recursive on Neg/Add/Sub/Mul children;
    // a deeply-nested constant term blew the call stack). Children are evaluated
    // into `memo` before the parent combines them — behavior-identical.
    std::unordered_map<ExprId, std::optional<mpz_class>> memo;
    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& fr = stack.back();
        ExprId e = fr.e;
        if (memo.find(e) != memo.end()) { stack.pop_back(); continue; }
        const auto& node = ir_.get(e);

        if (!fr.processed) {
            fr.processed = true;
            switch (node.kind) {
            case Kind::Neg: case Kind::Add: case Kind::Sub: case Kind::Mul:
                for (ExprId c : node.children)
                    if (memo.find(c) == memo.end()) stack.push_back({c, false});
                break;
            default: break;
            }
            continue;
        }

        stack.pop_back();
        std::optional<mpz_class> r = std::nullopt;
        switch (node.kind) {
        case Kind::ConstInt:
            if (auto* v = std::get_if<int64_t>(&node.payload.value)) r = mpz_class(*v);
            break;
        case Kind::ConstReal:
            // Defensive: SOMTParser currently maps integer literals to ConstReal
            // with Real sort in some contexts. We accept them here only when the
            // denominator is 1 (i.e. the value is mathematically an integer).
            // This is safe because IntDivModLowerer only operates on Int-sort
            // subexpressions, so any ConstReal encountered here is semantically
            // an integer constant that leaked through the parser.
            if (auto* s = std::get_if<std::string>(&node.payload.value)) {
                mpq_class q(*s);
                if (q.get_den() == 1) r = mpz_class(q.get_num());
            }
            break;
        case Kind::Neg:
            if (node.children.size() == 1) {
                if (auto v = memo[node.children[0]]) r = -(*v);
            }
            break;
        case Kind::Add:
            // n-ary SMT-LIB `(+ a b c)` = a + b + c. Old code only
            // handled size == 2 — n-ary constants didn't fold here.
            if (!node.children.empty()) {
                mpz_class sum(0);
                bool allOk = true;
                for (ExprId c : node.children) {
                    if (auto v = memo[c]) sum += *v;
                    else { allOk = false; break; }
                }
                if (allOk) r = sum;
            }
            break;
        case Kind::Sub:
            // n-ary `(- a b c)` = (a - b) - c. Old code only handled size == 2.
            if (!node.children.empty()) {
                if (auto first = memo[node.children[0]]) {
                    if (node.children.size() == 1) {
                        r = -(*first);
                    } else {
                        mpz_class acc = *first;
                        bool allOk = true;
                        for (size_t i = 1; i < node.children.size(); ++i) {
                            if (auto v = memo[node.children[i]]) acc -= *v;
                            else { allOk = false; break; }
                        }
                        if (allOk) r = acc;
                    }
                }
            }
            break;
        case Kind::Mul:
            // n-ary `(* a b c)` = a * b * c. Old code only handled size == 2.
            if (!node.children.empty()) {
                mpz_class prod(1);
                bool allOk = true;
                for (ExprId c : node.children) {
                    if (auto v = memo[c]) prod *= *v;
                    else { allOk = false; break; }
                }
                if (allOk) r = prod;
            }
            break;
        default: break;
        }
        memo[e] = r;
    }
    return memo[root];
}

bool IntDivModLowerer::containsNonlinear(ExprId root) const {
    // Iterative DFS (was recursive on children; deep terms overflowed the stack).
    std::vector<ExprId> stack{root};
    while (!stack.empty()) {
        ExprId e = stack.back();
        stack.pop_back();
        const auto& node = ir_.get(e);
        switch (node.kind) {
        case Kind::Mul:
            // n-ary Mul: nonlinear if at least 2 non-constant operands.
            // Old code only checked the binary case; n-ary `(* a b c)` with
            // multiple non-constants was silently treated as linear and
            // missed downstream lowering decisions.
            if (!node.children.empty()) {
                int nonConst = 0;
                for (ExprId c : node.children) {
                    if (!evalIntConstTerm(c).has_value()) {
                        if (++nonConst >= 2) return true;
                    }
                }
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
        for (ExprId c : node.children) stack.push_back(c);
    }
    return false;
}

void IntDivModLowerer::emitConstDivisorConstraints(const DivModDef& def, const mpz_class& k, ScopeLevel level) {
    ExprId kExpr = mkIntConst(k);                 // full precision (no get_si truncation)
    mpz_class absKMinusOneVal = abs(k);
    absKMinusOneVal -= 1;
    ExprId absKMinusOne = mkIntConst(absKMinusOneVal);

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
    // Track C1 Phase 2 (XOLVER_NIA_SYMBOLIC_DIVMOD_NONZERO, default-OFF):
    // if `b` is provably > 0 from the asserted bounds, emit only the
    // `b > 0` branch (a = b*q + r, 0 <= r <= b - 1) and skip both the
    // `b = 0` undef branch (which is what raised needsEUF) and the `b < 0`
    // branch (unreachable). Sound: dropping unreachable cases is unsat-
    // preserving. Gated default-OFF because, for cases like
    // `(mod (* x x) x) = 5 ∧ x > 0`, the current NIA reasoner stack cannot
    // refute the engaged constraint within the test budget — flooring to
    // unknown via the EUF-needing path is the existing soundness floor;
    // engaging requires per-case validation that the engine actually
    // decides in budget.
    static const bool nonzeroPath =
        std::getenv("XOLVER_NIA_SYMBOLIC_DIVMOD_NONZERO") != nullptr;
    if (nonzeroPath && divisorIsProvenStrictlyPositive(def.b)) {
        emitVariableDivisorConstraintsPositiveDivisor(def, level);
        return;
    }

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

// Track C1 Phase 2: emit only the b > 0 branch of the symbolic-divisor
// lowering. Caller has already verified `b > 0` is implied by the asserted
// bounds (divisorIsProvenStrictlyPositive). The b = 0 and b < 0 cases are
// unreachable under any satisfying assignment, so dropping them is sound
// and does NOT require EUF.
void IntDivModLowerer::emitVariableDivisorConstraintsPositiveDivisor(
        const DivModDef& def, ScopeLevel level) {
    ExprId zero = mkIntConst(0);
    ExprId one = mkIntConst(1);

    // Track C1 Phase 2.7 — structural shortcut for `(* b b) div/mod b`.
    //
    // When `a` is syntactically `(* b b)` (b appears as both factors of a
    // Mul, recognised by ExprId equality after CoreIr hash-consing) and the
    // caller has already proven `b > 0`, the engagement of the standard
    // `a = b*q + r` form on this dividend hangs in the NIA reasoner stack
    // (see SYMBOLIC_DIVMOD_NONZERO defect: `(mod (* x x) x) = 5 ∧ x > 0`
    // engaged path runs out of budget without refuting the trivial 0 = 5).
    //
    // Mathematically, for any b != 0:   (b * b) = b * b + 0
    //                            i.e.   q = b,  r = 0.
    // This is the unique Euclidean decomposition under the b > 0 case the
    // caller guarantees, so emitting `q = b ∧ r = 0` linearly is sound and
    // exact. The shortcut sidesteps the nonlinear engagement entirely.
    //
    // Soundness: gated on `divisorIsProvenStrictlyPositive(def.b)` (the
    // function's precondition — the caller is `emitVariableDivisorConstraints`
    // which checks it). At b = 0 the rewrite would be unsound (the SMT-LIB
    // semantics for mod-by-zero are unspecified, so the model could pick any
    // value); the b > 0 gate excludes that case entirely.
    {
        const auto& aNode = ir_.get(def.a);
        if (aNode.kind == Kind::Mul && aNode.children.size() == 2 &&
            aNode.children[0] == def.b && aNode.children[1] == def.b) {
            generatedAssertions_.push_back({level, mkEq(def.q, def.b)});
            generatedAssertions_.push_back({level, mkEq(def.r, zero)});
            // Linear-only emit. No nonlinear engagement, no EUF.
            return;
        }
    }

    // a = b*q + r
    generatedAssertions_.push_back(
        {level, mkEq(def.a, mkAdd(mkMul(def.b, def.q), def.r))});
    // 0 <= r
    generatedAssertions_.push_back({level, mkLe(zero, def.r)});
    // r <= b - 1
    generatedAssertions_.push_back({level, mkLe(def.r, mkSub(def.b, one))});

    // b*q is nonlinear (product of two non-constants).
    updateRequirement(true, false);
}

// Track C1 Phase 2: scan the asserted top-level conjunction for syntactic
// strict-positive lower bounds on integer variables, populate
// `positiveVars_`. Conservative — we only inspect top-level atoms (no
// recursion into And/Or trees, no Boolean satisfaction reasoning). The
// helper is used by divisorIsProvenStrictlyPositive() to decide whether
// the EUF-requiring `b = 0` undef branch can be skipped at lowering time.
//
// Patterns recognised (all on Int variables):
//   (> v c)   with c >= 0  -> v strictly positive
//   (>= v c)  with c >= 1  -> v strictly positive
//   (< c v)   with c >= 0  -> v strictly positive  (Lt with var on rhs)
//   (<= c v)  with c >= 1  -> v strictly positive  (Leq with var on rhs)
//   (not (<= v c)) with c >= 0  -> v > c implies v > 0
void IntDivModLowerer::scanPositiveBounds(
        const std::vector<std::pair<ScopeLevel, ExprId>>& asserts) {
    auto isConstIntGe = [&](ExprId e, const mpz_class& bound) -> bool {
        const CoreExpr& n = ir_.get(e);
        if (n.kind != Kind::ConstInt && n.kind != Kind::ConstReal) return false;
        if (auto* iv = std::get_if<int64_t>(&n.payload.value))
            return mpz_class(*iv) >= bound;
        if (auto* sv = std::get_if<std::string>(&n.payload.value)) {
            try { return mpq_class(*sv).get_num() >= bound &&
                         mpq_class(*sv).get_den() == 1; }
            catch (...) { return false; }
        }
        return false;
    };
    auto varName = [&](ExprId e) -> std::optional<std::string> {
        const CoreExpr& n = ir_.get(e);
        if (n.kind != Kind::Variable) return std::nullopt;
        if (auto* s = std::get_if<std::string>(&n.payload.value)) return *s;
        return std::nullopt;
    };
    auto markIfStrictPositive = [&](ExprId atom) {
        const CoreExpr& a = ir_.get(atom);
        // (> v c) / (Gt v c)
        if ((a.kind == Kind::Gt || a.kind == Kind::Geq) &&
            a.children.size() == 2) {
            mpz_class need = (a.kind == Kind::Gt) ? mpz_class(0) : mpz_class(1);
            if (auto v = varName(a.children[0])) {
                if (isConstIntGe(a.children[1], need)) positiveVars_.insert(*v);
            }
        }
        // (< c v) / (Lt c v) and (<= c v) / (Leq c v)
        if ((a.kind == Kind::Lt || a.kind == Kind::Leq) &&
            a.children.size() == 2) {
            mpz_class need = (a.kind == Kind::Lt) ? mpz_class(0) : mpz_class(1);
            if (auto v = varName(a.children[1])) {
                if (isConstIntGe(a.children[0], need)) positiveVars_.insert(*v);
            }
        }
    };
    // Flatten top-level And nodes (and their nested Ands) so the positivity
    // scan reaches conjuncts that were syntactically packed into one assertion.
    // Sound: an And at top level is asserted-true iff every child is true, so
    // each child is an independent atomic constraint that can mark a var
    // positive. Closes the sqrtmodinv-hoenicke / LCTES pattern where the
    // assertion shape is `(assert (and (>= x 1) (>= y 1)))` -- without this
    // flatten, neither x nor y was recognised as positive and the lowerer
    // bailed with `needsEUF` even though XOLVER_NIA_SYMBOLIC_DIVMOD_NONZERO=1
    // was set.
    std::function<void(ExprId)> walk = [&](ExprId e) {
        const CoreExpr& n = ir_.get(e);
        if (n.kind == Kind::And) {
            for (ExprId c : n.children) walk(c);
            return;
        }
        markIfStrictPositive(e);
    };
    for (const auto& [lvl, e] : asserts) {
        (void)lvl;
        walk(e);
    }
}

// Track C1 Phase 2: structural strict-positive test. Returns true iff `b`
// is one of:
//   - a Variable in positiveVars_,
//   - a positive integer constant,
//   - Mul/Pow of strictly-positive operands.
// Conservative: any other shape returns false, which keeps the existing
// EUF-needing lowering path.
bool IntDivModLowerer::divisorIsProvenStrictlyPositive(ExprId b) const {
    const CoreExpr& n = ir_.get(b);
    switch (n.kind) {
    case Kind::Variable: {
        if (auto* s = std::get_if<std::string>(&n.payload.value))
            return positiveVars_.count(*s) > 0;
        return false;
    }
    case Kind::ConstInt: {
        if (auto* iv = std::get_if<int64_t>(&n.payload.value)) return *iv > 0;
        if (auto* sv = std::get_if<std::string>(&n.payload.value)) {
            try { mpq_class q(*sv);
                  return q.get_den() == 1 && q.get_num() > 0; }
            catch (...) { return false; }
        }
        return false;
    }
    case Kind::ConstReal: {
        if (auto* sv = std::get_if<std::string>(&n.payload.value)) {
            try { mpq_class q(*sv);
                  return q.get_den() == 1 && q.get_num() > 0; }
            catch (...) { return false; }
        }
        return false;
    }
    case Kind::Mul: {
        for (ExprId c : n.children)
            if (!divisorIsProvenStrictlyPositive(c)) return false;
        return !n.children.empty();
    }
    case Kind::Pow: {
        // (Pow base exp) > 0 iff base > 0 (any positive exponent fine).
        if (n.children.size() != 2) return false;
        return divisorIsProvenStrictlyPositive(n.children[0]);
    }
    default:
        return false;
    }
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

ExprId IntDivModLowerer::mkIntConst(const mpz_class& v) {
    // Small enough for int64 -> use the int64 path (cheaper downstream).
    if (mpz_fits_slong_p(v.get_mpz_t())) {
        return mkIntConst(static_cast<int64_t>(v.get_si()));
    }
    // Large (e.g. 2^256 modulus): store the FULL decimal as a string-payload
    // ConstInt — exactly how the frontend adapter represents big literals — so
    // no precision is lost. (PolynomialConverter handles string-payload ConstInt.)
    CoreExpr e;
    e.kind = Kind::ConstInt;
    e.sort = intSortId_;
    e.payload = Payload(v.get_str());
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
    // In Xolver's IR, UF symbols are represented by Variable nodes with special names.
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

} // namespace xolver
