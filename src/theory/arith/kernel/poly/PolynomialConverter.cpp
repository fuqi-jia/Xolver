#include "util/MpqUtils.h"
#include "theory/arith/kernel/poly/PolynomialConverter.h"
#include "util/MpqUtils.h"
#include "expr/payload.h"
#include <cassert>
#include <gmpxx.h>

namespace xolver {

// ============================================================================
// Public API
// ============================================================================

PolynomialConverter::ConvertedExpr PolynomialConverter::convert(
    ExprId eid, const CoreIr& ir) {
    memo_.clear();
    preCollectIterative(eid, ir);
    auto rpOpt = collectRec(eid, ir);
    if (!rpOpt) return {};
    rpOpt->normalize();

    auto norm = rpOpt->toPrimitiveInteger(kernel_);
    if (!norm.ok()) return {};

    return {norm.poly, norm.scale};
}

PolynomialConverter::ConvertedConstraint PolynomialConverter::convertConstraint(
    ExprId lhs, ExprId rhs, Relation rel, const CoreIr& ir) {
    memo_.clear();
    preCollectIterative(lhs, ir);
    preCollectIterative(rhs, ir);
    auto rpLOpt = collectRec(lhs, ir);
    auto rpROpt = collectRec(rhs, ir);

    if (!rpLOpt || !rpROpt) {
        return {PolyConstraintStatus::UnsupportedNonPolynomial, NullPoly};
    }

    RationalPolynomial diff = *rpLOpt - *rpROpt;
    diff.normalize();

    // Zero-polynomial immediate simplification
    if (diff.isZero()) {
        switch (rel) {
            case Relation::Eq:
            case Relation::Leq:
            case Relation::Geq:
                return {PolyConstraintStatus::Tautology, NullPoly};
            case Relation::Neq:
            case Relation::Lt:
            case Relation::Gt:
                return {PolyConstraintStatus::Conflict, NullPoly};
        }
    }

    auto norm = diff.toPrimitiveInteger(kernel_);
    if (!norm.ok()) return {PolyConstraintStatus::Failure, NullPoly};

    // scale > 0, so relation direction is preserved.
    return {PolyConstraintStatus::Constraint, norm.poly};
}

// ============================================================================
// Recursive collection
// ============================================================================

std::optional<RationalPolynomial> PolynomialConverter::collectRec(
    ExprId eid, const CoreIr& ir) {
    auto it = memo_.find(eid);
    if (it != memo_.end()) return it->second;

    const CoreExpr& e = ir.get(eid);
    std::optional<RationalPolynomial> result;

    switch (e.kind) {
        case Kind::ConstInt: {
            if (auto* i = std::get_if<int64_t>(&e.payload.value)) {
                result = RationalPolynomial::fromConstant(mpq_class(*i));
            } else if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                // Large integer literals (e.g. EVM 2^256 constants) do not fit
                // int64 and are stored as decimal strings — parse at full
                // precision (mirrors the ConstReal path) rather than dropping them.
                result = RationalPolynomial::fromConstant(mpqFromString(*s));
            }
            break;
        }
        case Kind::ConstReal: {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                result = RationalPolynomial::fromConstant(mpqFromString(*s));
            }
            break;
        }
        case Kind::Variable: {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                VarId v = kernel_.getOrCreateVar(*s);
                result = RationalPolynomial::fromVar(v, 1, mpq_class(1));
            }
            break;
        }
        case Kind::Add: {
            if (e.children.size() >= 2) {
                auto first = collectRec(e.children[0], ir);
                if (!first) { result = std::nullopt; break; }
                RationalPolynomial acc = std::move(*first);
                bool ok = true;
                for (size_t i = 1; i < e.children.size(); ++i) {
                    auto next = collectRec(e.children[i], ir);
                    if (!next) { result = std::nullopt; ok = false; break; }
                    acc.appendTerms(*next);   // batch; canonicalize once below
                }
                if (ok) { acc.normalize(); if (!result.has_value()) result = std::move(acc); }
            }
            break;
        }
        case Kind::Sub: {
            // SMT-LIB n-ary `(- a b c ...)` parses left-associatively as
            // `((a - b) - c) - ...`. The old code only handled size == 2,
            // silently dropping size >= 3 cases — every formula containing
            // a 3-arg `(- a b c)` rejected with "[ATOM] unsupported NRA/NIA
            // kind=21" because the polynomial converter returned nullopt
            // → atom marked unsupported → solver returns unknown without
            // any reasoning. This was a long-standing parser blind spot.
            if (e.children.empty()) break;
            if (e.children.size() == 1) {
                // Unary `(- a)` — same as Neg.
                auto sub = collectRec(e.children[0], ir);
                if (!sub) { result = std::nullopt; break; }
                result = -(*sub);
                break;
            }
            auto first = collectRec(e.children[0], ir);
            if (!first) { result = std::nullopt; break; }
            RationalPolynomial running = std::move(*first);
            bool ok = true;
            for (size_t i = 1; i < e.children.size(); ++i) {
                auto next = collectRec(e.children[i], ir);
                if (!next) { ok = false; break; }
                running.appendTerms(*next, /*negate=*/true);   // batch subtract
            }
            if (ok) { running.normalize(); result = std::move(running); }
            break;
        }
        case Kind::Neg: {
            if (e.children.size() == 1) {
                auto sub = collectRec(e.children[0], ir);
                if (!sub) { result = std::nullopt; break; }
                result = -(*sub);
            }
            break;
        }
        case Kind::Mul: {
            if (e.children.size() >= 2) {
                auto first = collectRec(e.children[0], ir);
                if (!first) { result = std::nullopt; break; }
                RationalPolynomial acc = std::move(*first);
                for (size_t i = 1; i < e.children.size(); ++i) {
                    auto next = collectRec(e.children[i], ir);
                    if (!next) { result = std::nullopt; break; }
                    acc = acc * (*next);
                }
                if (!result.has_value()) result = std::move(acc);
            }
            break;
        }
        case Kind::Div: {
            // Supported: polynomial / numeric constant(s)  ->  polynomial * (1/c1/c2/...)
            // Unsupported: polynomial / variable  or  polynomial / polynomial
            //
            // SMT-LIB n-ary `(/ a b c)` is `(a / b) / c` (left-associative);
            // the old code only handled size == 2 and silently dropped n >= 3
            // — same parser blind-spot pattern as Kind::Sub.
            if (e.children.size() < 2) break;
            auto num = collectRec(e.children[0], ir);
            if (!num) { result = std::nullopt; break; }
            // Accumulate each divisor as a constant; bail if any divisor isn't.
            auto tryGetConst = [&](ExprId denId, mpq_class& out) -> bool {
                const CoreExpr& denNode = ir.get(denId);
                if (denNode.kind == Kind::ConstInt) {
                    if (auto* i = std::get_if<int64_t>(&denNode.payload.value)) {
                        if (*i == 0) return false;
                        out = mpq_class(1, *i);
                        return true;
                    } else if (auto* s = std::get_if<std::string>(&denNode.payload.value)) {
                        mpq_class q = mpqFromString(*s);
                        if (q == 0) return false;
                        out = mpq_class(1) / q;
                        return true;
                    }
                } else if (denNode.kind == Kind::ConstReal) {
                    if (auto* s = std::get_if<std::string>(&denNode.payload.value)) {
                        mpq_class q(*s);
                        if (q == 0) return false;
                        out = mpq_class(1) / q;
                        return true;
                    }
                }
                return false;
            };
            RationalPolynomial rp = std::move(*num);
            bool ok = true;
            for (size_t i = 1; i < e.children.size(); ++i) {
                mpq_class invDen;
                if (!tryGetConst(e.children[i], invDen)) { ok = false; break; }
                rp *= invDen;
            }
            if (ok) result = std::move(rp);
            else    result = std::nullopt;
            break;
        }
        case Kind::Pow: {
            if (e.children.size() == 2) {
                auto base = collectRec(e.children[0], ir);
                if (!base) { result = std::nullopt; break; }
                const CoreExpr& expNode = ir.get(e.children[1]);
                std::optional<int64_t> expInt;
                if (expNode.kind == Kind::ConstInt) {
                    if (auto* i = std::get_if<int64_t>(&expNode.payload.value)) {
                        expInt = *i;
                    }
                } else if (expNode.kind == Kind::ConstReal) {
                    // SOMTParser frequently emits integer literals as ConstReal
                    // (sort = IntOrReal). Accept those whose denominator is 1.
                    if (auto* s = std::get_if<std::string>(&expNode.payload.value)) {
                        try {
                            mpq_class q = mpqFromString(*s);
                            if (q.get_den() == 1 && q.get_num().fits_slong_p()) {
                                expInt = q.get_num().get_si();
                            }
                        } catch (...) {
                            // leave expInt unset; we fall through to "unsupported"
                        }
                    }
                }
                if (!expInt) {
                    result = std::nullopt;  // non-integer or non-constant exponent
                } else if (*expInt < 0) {
                    result = std::nullopt;  // negative exponent unsupported in polynomial ring
                } else {
                    result = base->pow(static_cast<uint32_t>(*expInt));
                }
            }
            break;
        }
        case Kind::ToReal: {
            // to_real is a transparent coercion from Int to Real.
            if (e.children.size() == 1) {
                result = collectRec(e.children[0], ir);
            }
            break;
        }
        case Kind::ToInt: {
            // Supported: to_int(constant) -> floor(constant)
            if (e.children.size() == 1) {
                const CoreExpr& arg = ir.get(e.children[0]);
                if (arg.kind == Kind::ConstInt) {
                    if (auto* v = std::get_if<int64_t>(&arg.payload.value)) {
                        result = RationalPolynomial::fromConstant(mpq_class(*v));
                    } else if (auto* s = std::get_if<std::string>(&arg.payload.value)) {
                        result = RationalPolynomial::fromConstant(mpqFromString(*s));  // to_int(int)=int
                    }
                } else if (arg.kind == Kind::ConstReal) {
                    if (auto* s = std::get_if<std::string>(&arg.payload.value)) {
                        mpq_class q(*s);
                        mpz_class z = q.get_num() / q.get_den();
                        if (q < 0 && q.get_num() % q.get_den() != 0) {
                            z -= 1;
                        }
                        result = RationalPolynomial::fromConstant(mpq_class(z));
                    }
                }
            }
            break;
        }
        default:
            // Non-arithmetic or unsupported node
            result = std::nullopt;
            break;
    }

    memo_[eid] = result;
    return result;
}

void PolynomialConverter::preCollectIterative(ExprId root, const CoreIr& ir) {
    // Bottom-up pre-pass: memoize every arithmetic subterm collectRec recurses
    // into before collectRec(root) runs, so the (memoized) collectRec resolves
    // each child from memo_ and never recurses deeper than one level. Pushes
    // exactly collectRec's recursion targets (Add/Sub/Mul: all children;
    // Neg/ToReal/Div/Pow: child[0] only — denominator/exponent are read, not
    // collected). collectRec is idempotent (getOrCreateVar is too), so warming
    // the memo bottom-up is behavior-identical.
    struct Frame { ExprId eid; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});
    while (!stack.empty()) {
        Frame& fr = stack.back();
        ExprId eid = fr.eid;
        if (memo_.find(eid) != memo_.end()) { stack.pop_back(); continue; }
        const CoreExpr& e = ir.get(eid);
        if (!fr.processed) {
            fr.processed = true;
            auto push = [&](ExprId c) {
                if (c != NullExpr && memo_.find(c) == memo_.end()) stack.push_back({c, false});
            };
            switch (e.kind) {
                case Kind::Add: case Kind::Sub: case Kind::Mul:
                    for (ExprId c : e.children) push(c);
                    break;
                case Kind::Neg: case Kind::ToReal: case Kind::Div: case Kind::Pow:
                    if (!e.children.empty()) push(e.children[0]);
                    break;
                default: break;
            }
            continue;
        }
        stack.pop_back();
        collectRec(eid, ir);  // children memoized -> recursion bounded to depth 1
    }
}

} // namespace xolver
