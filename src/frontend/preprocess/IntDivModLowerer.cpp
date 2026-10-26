#include "base/RuntimeConfig.h"
#include "frontend/preprocess/IntDivModLowerer.h"
#include "base/EnvParam.h"
#include <cassert>
#include <algorithm>
#include <iostream>
#include <unordered_set>

namespace xolver {

IntDivModLowerer::IntDivModLowerer(NativeTerms& ir)
    : ir_(ir), boolSortId_(ir.boolSortId()), intSortId_(ir.intSortId()) {
}

bool IntDivModLowerer::run() {
    requirement_ = {};
    generatedAssertions_.clear();
    origins_.clear();
    registry_.clear();
    memo_.clear();
    nonzeroFacts_.clear();
    divisorDomains_.clear();
    loweredAssertions_.clear();

    auto scoped = ir_.getScopedAssertions();
    for (const auto& [level, assertion] : scoped)
        collectNonzeroFacts(assertion, level);
    std::vector<std::pair<ScopeLevel, ExprId>> loweredScoped;

    for (const auto& [level, a] : scoped) {
        memo_.clear();
        ExprId lowered = lowerRec(a, level);
        if (requirement_.unsupported) {
            return false;
        }
        loweredScoped.push_back({level, lowered});
    }

    emitRemainderRelations();
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
        // ir_.addShared(), which can reallocate exprs_ and invalidate references.
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
                // ITE should have been eliminated by IteLowerer.
                std::cerr << "[IntDivModLowerer] ERROR: Kind::Ite not lowered before div/mod lowering\n";
                assert(false && "ITE should be eliminated before IntDivModLowerer");
            }
            memo_[e] = rebuilt;
        }
        if (auto fact = nonzeroFacts_.find(e); fact != nonzeroFacts_.end()) {
            const auto factLevel = fact->second;
            auto [entry, inserted] = nonzeroFacts_.try_emplace(memo_.at(e), factLevel);
            if (!inserted) entry->second = std::min(entry->second, factLevel);
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
        def.q = ir_.makeFreshVariable(intSortId_, "__nlc_div_q", /*routingAuxiliary=*/true);
        def.r = ir_.makeFreshVariable(intSortId_, "__nlc_mod_r", /*routingAuxiliary=*/true);
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

    TermExpr ne;
    ne.kind = node.kind;
    ne.sort = node.sort;
    for (ExprId c : newChildren) ne.children.push_back(c);
    ne.payload = node.payload;
    return ir_.addShared(std::move(ne));
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
            else if (auto* text = std::get_if<std::string>(&node.payload.value)) {
                mpz_class value;
                if (value.set_str(*text, 10) == 0) r = std::move(value);
            }
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
    std::unordered_set<ExprId> seen;
    while (!stack.empty()) {
        ExprId e = stack.back();
        stack.pop_back();
        if (!seen.insert(e).second) continue;
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

void IntDivModLowerer::emitRemainderRelations() {
    struct Remainder {
        ScopeLevel level;
        ExprId dividend;
        ExprId variable;
        mpz_class modulus;
    };
    std::vector<Remainder> remainders;
    for (const auto& [key, def] : registry_) {
        const auto divisor = evalIntConstTerm(def.b);
        if (!divisor || *divisor == 0 || !def.arithmeticConstraintsEmitted) continue;
        remainders.push_back({key.level, def.a, def.r, mpz_class(abs(*divisor))});
    }
    std::sort(remainders.begin(), remainders.end(), [](const auto& a, const auto& b) {
        if (a.level != b.level) return a.level < b.level;
        if (a.dividend != b.dividend) return a.dividend < b.dividend;
        if (a.modulus != b.modulus) return a.modulus < b.modulus;
        return a.variable < b.variable;
    });
    for (size_t i = 0; i < remainders.size(); ++i) {
        const auto& small = remainders[i];
        // One edge to the nearest available multiple keeps generated syntax
        // linear in the number of divisions. A divisibility chain transports
        // every remainder range without a quadratic family of extra atoms.
        for (size_t j = i + 1; j < remainders.size(); ++j) {
            const auto& large = remainders[j];
            if (small.level != large.level || small.dividend != large.dividend) break;
            if (!mpz_divisible_p(large.modulus.get_mpz_t(), small.modulus.get_mpz_t())) continue;
            if (large.modulus == small.modulus) {
                generatedAssertions_.push_back({small.level, mkEq(small.variable, large.variable)});
            } else {
                // Euclidean remainders are nonnegative even for negative
                // dividends/divisors. For m|n, r_n-r_m is a nonnegative
                // multiple of m. Exclude its first lattice gap directly,
                // without introducing another integer quotient to branch on.
                const auto equal = mkEq(large.variable, small.variable);
                const auto next = mkAdd(small.variable, mkIntConst(small.modulus));
                generatedAssertions_.push_back({small.level, mkOr(equal, mkLe(next, large.variable))});
                const mpz_class span = large.modulus - small.modulus;
                generatedAssertions_.push_back({small.level,
                    mkLe(large.variable, mkAdd(small.variable, mkIntConst(span)))});
            }
            break;
        }
    }
}

void IntDivModLowerer::emitVariableDivisorConstraints(const DivModDef& def, ScopeLevel level) {
    // A mandatory finite divisor domain permits an exact guarded linear
    // expansion. Keep its source disjunction and scope; zero still denotes
    // a congruent, otherwise unconstrained function.
    if (auto domain = divisorDomains_.find(def.b);
        domain != divisorDomains_.end() && domain->second.level <= level) {
        for (const auto& value : domain->second.values) {
            auto branch = def;
            branch.b = mkIntConst(value);
            const auto guard = mkNot(mkEq(def.b, branch.b));
            const auto begin = generatedAssertions_.size();
            if (value == 0) emitUndefZeroConstraints(branch, level);
            else emitConstDivisorConstraints(branch, value, level);
            for (auto i = begin; i < generatedAssertions_.size(); ++i)
                generatedAssertions_[i].expr = mkOr(guard, generatedAssertions_[i].expr);
        }
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
    const bool nonzero = knownNonzero(def.b, level);
    if (!nonzero) {
        ExprId qUndef = mkEq(def.q, mkUndefDivApp(def.a, def.b));
        ExprId rUndef = mkEq(def.r, mkUndefModApp(def.a, def.b));
        generatedAssertions_.push_back({level, mkOr(mkNot(bEqZero), qUndef)});
        generatedAssertions_.push_back({level, mkOr(mkNot(bEqZero), rUndef)});
    }

    // b > 0 => a = b*q + r, 0 <= r, r <= b - 1
    generatedAssertions_.push_back({level, mkOr(mkNot(bGtZero), equation)});
    generatedAssertions_.push_back({level, mkOr(mkNot(bGtZero), mkLe(zero, def.r))});
    generatedAssertions_.push_back({level, mkOr(mkNot(bGtZero), mkLe(def.r, mkSub(def.b, one)))});

    // b < 0 => a = b*q + r, 0 <= r, r <= -b - 1
    generatedAssertions_.push_back({level, mkOr(mkNot(bLtZero), equation)});
    generatedAssertions_.push_back({level, mkOr(mkNot(bLtZero), mkLe(zero, def.r))});
    generatedAssertions_.push_back({level, mkOr(mkNot(bLtZero), mkLe(def.r, mkSub(mkNeg(def.b), one)))});

    // Remainder bound: (b > 0 AND a >= 0) => r <= a. Sound — for b > 0, a >= 0
    // the quotient q = floor(a/b) >= 0, so a = b*q + r >= r. Lets linear/
    // difference reasoning refute `(a mod b) > a`-style goals that the
    // 0 <= r < b bounds alone cannot (Zohar int_check bvurem class).
    generatedAssertions_.push_back(
        {level, mkOr(mkNot(bGtZero),
                     mkOr(mkNot(mkLe(zero, def.a)), mkLe(def.r, def.a)))});
    // Quotient bound: (b > 0 AND a >= 0) => q <= a. Sound — q = floor(a/b) and
    // b >= 1, so q <= a. Refutes `(a div b) > a`-style goals (int_check bvudiv).
    generatedAssertions_.push_back(
        {level, mkOr(mkNot(bGtZero),
                     mkOr(mkNot(mkLe(zero, def.a)), mkLe(def.q, def.a)))});

    updateRequirement(true, !nonzero);
}

void IntDivModLowerer::collectNonzeroFacts(ExprId root, ScopeLevel level) {
    std::vector<ExprId> work{root};
    std::unordered_set<ExprId> seen;
    while (!work.empty()) {
        const auto id = work.back();
        work.pop_back();
        if (!seen.insert(id).second) continue;
        auto node = ir_.get(id);
        if (node.kind == Kind::And) {
            work.insert(work.end(), node.children.begin(), node.children.end());
            continue;
        }
        if (node.kind == Kind::Or) {
            collectFiniteDomain(id, level);
            continue;
        }
        bool negate = node.kind == Kind::Not && node.children.size() == 1;
        if (negate) node = ir_.get(node.children[0]);
        if (node.children.size() != 2) continue;
        for (bool reverse : {false, true}) {
            const auto term = node.children[reverse ? 1 : 0];
            if (ir_.get(term).sort != intSortId_) continue;
            auto value = evalIntConstTerm(node.children[reverse ? 0 : 1]);
            if (!value) continue;
            auto kind = node.kind;
            if (reverse) {
                if (kind == Kind::Lt) kind = Kind::Gt;
                else if (kind == Kind::Leq) kind = Kind::Geq;
                else if (kind == Kind::Gt) kind = Kind::Lt;
                else if (kind == Kind::Geq) kind = Kind::Leq;
            }
            if (negate) {
                if (kind == Kind::Lt) kind = Kind::Geq;
                else if (kind == Kind::Leq) kind = Kind::Gt;
                else if (kind == Kind::Gt) kind = Kind::Leq;
                else if (kind == Kind::Geq) kind = Kind::Lt;
                else if (kind == Kind::Eq) kind = Kind::Distinct;
                else if (kind == Kind::Distinct) kind = Kind::Eq;
            }
            const bool proven = (kind == Kind::Eq && *value != 0) ||
                (kind == Kind::Distinct && *value == 0) ||
                (kind == Kind::Gt && *value >= 0) || (kind == Kind::Geq && *value >= 1) ||
                (kind == Kind::Lt && *value <= 0) || (kind == Kind::Leq && *value <= -1);
            if (proven) {
                auto [entry, inserted] = nonzeroFacts_.try_emplace(term, level);
                if (!inserted) entry->second = std::min(entry->second, level);
            }
        }
    }
}

void IntDivModLowerer::collectFiniteDomain(ExprId root, ScopeLevel level) {
    std::vector<ExprId> work{root};
    std::unordered_set<ExprId> seen;
    ExprId term = NullExpr;
    std::vector<mpz_class> values;
    while (!work.empty()) {
        const auto id = work.back(); work.pop_back();
        if (!seen.insert(id).second) continue;
        const auto node = ir_.get(id);
        if (node.kind == Kind::Or) {
            work.insert(work.end(), node.children.begin(), node.children.end());
            continue;
        }
        if (node.kind == Kind::ConstBool) {
            if (auto value = std::get_if<bool>(&node.payload.value); value && !*value) continue;
            return;
        }
        if (node.kind != Kind::Eq || node.children.size() != 2) return;
        auto left = evalIntConstTerm(node.children[0]);
        auto right = evalIntConstTerm(node.children[1]);
        if (left && right) {
            if (*left == *right) return;
            continue;
        }
        if (!left && !right) return;
        const auto expression = node.children[left ? 1 : 0];
        if (ir_.get(expression).sort != intSortId_) return;
        if (term != NullExpr && term != expression) return;
        term = expression;
        values.push_back(left ? *left : *right);
    }
    if (term == NullExpr) return;
    std::sort(values.begin(), values.end());
    values.erase(std::unique(values.begin(), values.end()), values.end());
    auto found = divisorDomains_.find(term);
    if (found == divisorDomains_.end() || level < found->second.level ||
        (level == found->second.level && values.size() < found->second.values.size()))
        divisorDomains_.insert_or_assign(term, FiniteDomainFact{level, std::move(values)});
}

bool IntDivModLowerer::knownNonzero(ExprId root, ScopeLevel level) const {
    std::vector<ExprId> work{root};
    std::unordered_map<ExprId, bool> visited;
    while (!work.empty()) {
        auto id = work.back(); work.pop_back();
        if (!visited.emplace(id, true).second) continue;
        if (auto fact = nonzeroFacts_.find(id); fact != nonzeroFacts_.end() && fact->second <= level)
            continue;
        if (auto constant = evalIntConstTerm(id)) {
            if (*constant == 0) return false;
            continue;
        }
        auto node = ir_.get(id);
        if ((node.kind == Kind::Neg || node.kind == Kind::Abs) && node.children.size() == 1)
            work.push_back(node.children[0]);
        else if (node.kind == Kind::Mul && !node.children.empty())
            work.insert(work.end(), node.children.begin(), node.children.end());
        else if (node.kind == Kind::Ite && node.children.size() == 3) {
            work.push_back(node.children[1]); work.push_back(node.children[2]);
        } else return false;
    }
    return true;
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
    TermExpr e;
    e.kind = Kind::ConstInt;
    e.sort = intSortId_;
    e.payload = Payload(v);
    return ir_.addShared(std::move(e));
}

ExprId IntDivModLowerer::mkIntConst(const mpz_class& v) {
    // Small enough for int64 -> use the int64 path (cheaper downstream).
    if (mpz_fits_slong_p(v.get_mpz_t())) {
        return mkIntConst(static_cast<int64_t>(v.get_si()));
    }
    // Large (e.g. 2^256 modulus): store the FULL decimal as a string-payload
    // ConstInt — exactly how the frontend adapter represents big literals — so
    // no precision is lost. (PolynomialConverter handles string-payload ConstInt.)
    TermExpr e;
    e.kind = Kind::ConstInt;
    e.sort = intSortId_;
    e.payload = Payload(v.get_str());
    return ir_.addShared(std::move(e));
}

ExprId IntDivModLowerer::mkEq(ExprId a, ExprId b) {
    TermExpr e;
    e.kind = Kind::Eq;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId IntDivModLowerer::mkLe(ExprId a, ExprId b) {
    TermExpr e;
    e.kind = Kind::Leq;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId IntDivModLowerer::mkLt(ExprId a, ExprId b) {
    TermExpr e;
    e.kind = Kind::Lt;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId IntDivModLowerer::mkAdd(ExprId a, ExprId b) {
    TermExpr e;
    e.kind = Kind::Add;
    e.sort = intSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId IntDivModLowerer::mkSub(ExprId a, ExprId b) {
    TermExpr e;
    e.kind = Kind::Sub;
    e.sort = intSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId IntDivModLowerer::mkMul(ExprId a, ExprId b) {
    TermExpr e;
    e.kind = Kind::Mul;
    e.sort = intSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId IntDivModLowerer::mkNeg(ExprId a) {
    TermExpr e;
    e.kind = Kind::Neg;
    e.sort = intSortId_;
    e.children.push_back(a);
    return ir_.addShared(std::move(e));
}

ExprId IntDivModLowerer::mkOr(ExprId a, ExprId b) {
    TermExpr e;
    e.kind = Kind::Or;
    e.sort = boolSortId_;
    e.children.push_back(a);
    e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId IntDivModLowerer::mkNot(ExprId a) {
    TermExpr e;
    e.kind = Kind::Not;
    e.sort = boolSortId_;
    e.children.push_back(a);
    return ir_.addShared(std::move(e));
}

// ---------------------------------------------------------------------------
// EUF symbol management
// ---------------------------------------------------------------------------

ExprId IntDivModLowerer::getOrCreateUndefDivSymbol() {
    if (undefDivSym_ != NullExpr) return undefDivSym_;
    // Create a placeholder Variable node to serve as the UF symbol name carrier.
    // In Xolver's IR, UF symbols are represented by Variable nodes with special names.
    TermExpr e;
    e.kind = Kind::Variable;
    e.sort = intSortId_;
    e.payload = Payload(std::string("__undef_div"));
    undefDivSym_ = ir_.addShared(std::move(e));
    return undefDivSym_;
}

ExprId IntDivModLowerer::getOrCreateUndefModSymbol() {
    if (undefModSym_ != NullExpr) return undefModSym_;
    TermExpr e;
    e.kind = Kind::Variable;
    e.sort = intSortId_;
    e.payload = Payload(std::string("__undef_mod"));
    undefModSym_ = ir_.addShared(std::move(e));
    return undefModSym_;
}

ExprId IntDivModLowerer::mkUndefDivApp(ExprId a, ExprId b) {
    ExprId sym = getOrCreateUndefDivSymbol();
    TermExpr e;
    e.kind = Kind::UFApply;
    e.sort = intSortId_;
    e.children.push_back(sym);
    e.children.push_back(a);
    e.children.push_back(b);
    e.payload = Payload(std::string("__undef_div"));
    return ir_.addShared(std::move(e));
}

ExprId IntDivModLowerer::mkUndefModApp(ExprId a, ExprId b) {
    ExprId sym = getOrCreateUndefModSymbol();
    TermExpr e;
    e.kind = Kind::UFApply;
    e.sort = intSortId_;
    e.children.push_back(sym);
    e.children.push_back(a);
    e.children.push_back(b);
    e.payload = Payload(std::string("__undef_mod"));
    return ir_.addShared(std::move(e));
}

} // namespace xolver
