#include "util/MpqUtils.h"
#include "theory/arith/linear/LinearExpr.h"
#include "util/MpqUtils.h"
#include "expr/payload.h"
#include <cassert>
#include <algorithm>

namespace nlcolver {

bool extractLinearExpr(ExprId eid, const CoreIr& ir,
                       std::unordered_map<std::string, mpq_class>& coeffs,
                       mpq_class& constant,
                       const mpq_class& mul) {
    const CoreExpr& e = ir.get(eid);
    switch (e.kind) {
        case Kind::ConstInt: {
            if (auto* v = std::get_if<int64_t>(&e.payload.value)) {
                constant += mul * mpq_class(*v);
            }
            return true;
        }
        case Kind::ConstReal: {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                constant += mul * mpqFromString(*s);
            }
            return true;
        }
        case Kind::Variable: {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                coeffs[*s] += mul;
            }
            return true;
        }
        case Kind::Add: {
            for (ExprId child : e.children) {
                if (!extractLinearExpr(child, ir, coeffs, constant, mul)) return false;
            }
            return true;
        }
        case Kind::Sub: {
            // SMT-LIB '-' is variadic and left-associative:
            //   (- a)        == negation
            //   (- a b c ..) == a - b - c - ...
            // Handle any arity so we don't depend on the frontend binarizing.
            if (e.children.empty()) return false;
            if (e.children.size() == 1) {
                return extractLinearExpr(e.children[0], ir, coeffs, constant, -mul);
            }
            if (!extractLinearExpr(e.children[0], ir, coeffs, constant, mul)) return false;
            for (size_t i = 1; i < e.children.size(); ++i) {
                if (!extractLinearExpr(e.children[i], ir, coeffs, constant, -mul)) return false;
            }
            return true;
        }
        case Kind::Neg: {
            if (e.children.size() != 1) return false;
            return extractLinearExpr(e.children[0], ir, coeffs, constant, -mul);
        }
        case Kind::Mul: {
            // SMT-LIB '*' is variadic. Linear iff at most one factor is
            // non-constant; the constant factors fold into the multiplier.
            if (e.children.empty()) return false;
            mpq_class coeff = 1;
            bool haveNonConst = false;
            ExprId nonConst = e.children[0];  // overwritten iff a non-const is seen
            for (ExprId childId : e.children) {
                const CoreExpr& c = ir.get(childId);
                if (c.isConst()) {
                    if (auto* iv = std::get_if<int64_t>(&c.payload.value)) coeff *= mpq_class(*iv);
                    else if (auto* sv = std::get_if<std::string>(&c.payload.value)) coeff *= mpqFromString(*sv);
                    else return false;
                } else {
                    if (haveNonConst) return false;  // two non-const factors => nonlinear
                    haveNonConst = true;
                    nonConst = childId;
                }
            }
            if (!haveNonConst) {
                constant += mul * coeff;
                return true;
            }
            return extractLinearExpr(nonConst, ir, coeffs, constant, mul * coeff);
        }
        case Kind::Div: {
            // SMT-LIB '/' is variadic and left-associative:
            //   (/ a b c ..) == a / b / c / .. == a / (b*c*..)
            // Linear iff every denominator is a nonzero constant; the numerator
            // (children[0]) may be any linear expression. This subsumes the
            // const/const case. A non-constant denominator (x / y) is nonlinear.
            if (e.children.size() < 2) return false;
            mpq_class denProd = 1;
            for (size_t i = 1; i < e.children.size(); ++i) {
                const CoreExpr& d = ir.get(e.children[i]);
                if (!d.isConst()) return false;
                if (auto* iv = std::get_if<int64_t>(&d.payload.value)) denProd *= mpq_class(*iv);
                else if (auto* sv = std::get_if<std::string>(&d.payload.value)) denProd *= mpqFromString(*sv);
                else return false;
            }
            if (denProd == 0) return false;
            return extractLinearExpr(e.children[0], ir, coeffs, constant, mul / denProd);
        }
        case Kind::ToReal: {
            if (e.children.size() != 1) return false;
            return extractLinearExpr(e.children[0], ir, coeffs, constant, mul);
        }
        case Kind::ToInt: {
            // Supported cases:
            // 1. to_int(constant) -> floor(constant)
            // 2. to_int(integer_var) -> integer_var
            // All other cases (real vars, expressions) are unsupported.
            if (e.children.size() != 1) return false;
            const CoreExpr& arg = ir.get(e.children[0]);
            if (arg.kind == Kind::ConstInt) {
                if (auto* v = std::get_if<int64_t>(&arg.payload.value)) {
                    constant += mul * mpq_class(*v);
                }
                return true;
            }
            if (arg.kind == Kind::ConstReal) {
                if (auto* s = std::get_if<std::string>(&arg.payload.value)) {
                    mpq_class q(*s);
                    // floor for positive, ceil for negative
                    mpz_class z = q.get_num() / q.get_den();
                    if (q < 0 && q.get_num() % q.get_den() != 0) {
                        z -= 1;
                    }
                    constant += mul * mpq_class(z);
                }
                return true;
            }
            if (arg.kind == Kind::Variable) {
                auto sk = ir.sortKind(arg.sort);
                if (sk == SortKind::Int) {
                    if (auto* s = std::get_if<std::string>(&arg.payload.value)) {
                        coeffs[*s] += mul;
                    }
                    return true;
                }
            }
            return false;
        }
        default:
            return false;
    }
}

bool extractLinearConstraint(ExprId eid, const CoreIr& ir,
                              std::unordered_map<std::string, mpq_class>& coeffs,
                              mpq_class& rhs, Relation& rel) {
    const CoreExpr& e = ir.get(eid);
    if (e.children.size() != 2) return false;

    switch (e.kind) {
        case Kind::Eq:  rel = Relation::Eq;  break;
        case Kind::Lt:  rel = Relation::Lt;  break;
        case Kind::Leq: rel = Relation::Leq; break;
        case Kind::Gt:  rel = Relation::Gt;  break;
        case Kind::Geq: rel = Relation::Geq; break;
        case Kind::Distinct: rel = Relation::Neq; break;
        default: return false;
    }

    mpq_class constant = 0;
    if (!extractLinearExpr(e.children[0], ir, coeffs, constant, mpq_class(1))) return false;
    if (!extractLinearExpr(e.children[1], ir, coeffs, constant, mpq_class(-1))) return false;
    rhs = -constant;

    // Canonicalize: ensure the first non-zero coefficient (by var name) is positive.
    // This guarantees that e.g. "x >= 0" and "0 <= x" map to the same canonical form.
    // Use sorted order to ensure determinism (unordered_map iteration is non-deterministic).
    bool needFlip = false;
    std::string firstVar;
    for (const auto& [name, coeff] : coeffs) {
        if (coeff != 0) {
            if (firstVar.empty() || name < firstVar) {
                firstVar = name;
                needFlip = (coeff < 0);
            }
        }
    }
    if (needFlip) {
        for (auto& [name, coeff] : coeffs) {
            coeff = -coeff;
        }
        rhs = -rhs;
        switch (rel) {
            case Relation::Lt:  rel = Relation::Gt;  break;
            case Relation::Leq: rel = Relation::Geq; break;
            case Relation::Gt:  rel = Relation::Lt;  break;
            case Relation::Geq: rel = Relation::Leq; break;
            default: break; // Eq, Neq unchanged
        }
    }
    return true;
}

Relation negateRelation(Relation r) {
    switch (r) {
        case Relation::Eq:  return Relation::Neq;
        case Relation::Lt:  return Relation::Geq;
        case Relation::Leq: return Relation::Gt;
        case Relation::Gt:  return Relation::Leq;
        case Relation::Geq: return Relation::Lt;
        case Relation::Neq: return Relation::Eq;
    }
    return r;
}

} // namespace nlcolver
