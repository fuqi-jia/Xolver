#include "theory/arith/linear/LinearExpr.h"
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
                constant += mul * mpq_class(*s);
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
            if (e.children.size() != 2) return false;
            if (!extractLinearExpr(e.children[0], ir, coeffs, constant, mul)) return false;
            if (!extractLinearExpr(e.children[1], ir, coeffs, constant, -mul)) return false;
            return true;
        }
        case Kind::Neg: {
            if (e.children.size() != 1) return false;
            return extractLinearExpr(e.children[0], ir, coeffs, constant, -mul);
        }
        case Kind::Mul: {
            if (e.children.size() != 2) return false;
            const CoreExpr& a = ir.get(e.children[0]);
            const CoreExpr& b = ir.get(e.children[1]);
            if (a.isConst()) {
                mpq_class c;
                if (auto* iv = std::get_if<int64_t>(&a.payload.value)) c = mpq_class(*iv);
                else if (auto* sv = std::get_if<std::string>(&a.payload.value)) c = mpq_class(*sv);
                else return false;
                return extractLinearExpr(e.children[1], ir, coeffs, constant, mul * c);
            }
            if (b.isConst()) {
                mpq_class c;
                if (auto* iv = std::get_if<int64_t>(&b.payload.value)) c = mpq_class(*iv);
                else if (auto* sv = std::get_if<std::string>(&b.payload.value)) c = mpq_class(*sv);
                else return false;
                return extractLinearExpr(e.children[0], ir, coeffs, constant, mul * c);
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
