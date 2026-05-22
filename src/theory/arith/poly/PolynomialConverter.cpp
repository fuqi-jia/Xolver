#include "util/MpqUtils.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include "util/MpqUtils.h"
#include "expr/payload.h"
#include <cassert>
#include <gmpxx.h>

namespace nlcolver {

// ============================================================================
// Public API
// ============================================================================

PolynomialConverter::ConvertedExpr PolynomialConverter::convert(
    ExprId eid, const CoreIr& ir) {
    memo_.clear();
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
                for (size_t i = 1; i < e.children.size(); ++i) {
                    auto next = collectRec(e.children[i], ir);
                    if (!next) { result = std::nullopt; break; }
                    acc += *next;
                }
                if (!result.has_value()) result = std::move(acc);
            }
            break;
        }
        case Kind::Sub: {
            if (e.children.size() == 2) {
                auto l = collectRec(e.children[0], ir);
                auto r = collectRec(e.children[1], ir);
                if (!l || !r) { result = std::nullopt; break; }
                result = *l - *r;
            }
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
            // Supported: polynomial / numeric constant  ->  polynomial * (1/constant)
            // Unsupported: polynomial / variable  or  polynomial / polynomial
            if (e.children.size() == 2) {
                auto num = collectRec(e.children[0], ir);
                if (!num) { result = std::nullopt; break; }
                const CoreExpr& denNode = ir.get(e.children[1]);
                mpq_class denomValue;
                bool isConstantDenominator = false;
                if (denNode.kind == Kind::ConstInt) {
                    if (auto* i = std::get_if<int64_t>(&denNode.payload.value)) {
                        if (*i != 0) {
                            denomValue = mpq_class(1, *i);
                            isConstantDenominator = true;
                        }
                    }
                } else if (denNode.kind == Kind::ConstReal) {
                    if (auto* s = std::get_if<std::string>(&denNode.payload.value)) {
                        mpq_class q(*s);
                        if (q != 0) {
                            denomValue = mpq_class(1) / q;
                            isConstantDenominator = true;
                        }
                    }
                }
                if (!isConstantDenominator) {
                    result = std::nullopt;
                } else {
                    RationalPolynomial rp = std::move(*num);
                    rp *= denomValue;
                    result = std::move(rp);
                }
            }
            break;
        }
        case Kind::Pow: {
            if (e.children.size() == 2) {
                auto base = collectRec(e.children[0], ir);
                if (!base) { result = std::nullopt; break; }
                const CoreExpr& expNode = ir.get(e.children[1]);
                if (expNode.kind == Kind::ConstInt) {
                    if (auto* i = std::get_if<int64_t>(&expNode.payload.value)) {
                        if (*i >= 0) {
                            result = base->pow(static_cast<uint32_t>(*i));
                        } else {
                            result = std::nullopt; // negative exponent unsupported
                        }
                    }
                } else {
                    result = std::nullopt; // non-constant exponent unsupported
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

} // namespace nlcolver
