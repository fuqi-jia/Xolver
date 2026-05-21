#include "expr/Smt2Dumper.h"
#include <sstream>

namespace nlcolver {

static const char* kindToSMT2(Kind k) {
    switch (k) {
        case Kind::Not:       return "not";
        case Kind::And:       return "and";
        case Kind::Or:        return "or";
        case Kind::Implies:   return "=>";
        case Kind::Xor:       return "xor";
        case Kind::Ite:       return "ite";
        case Kind::Add:       return "+";
        case Kind::Sub:       return "-";
        case Kind::Neg:       return "-";
        case Kind::Mul:       return "*";
        case Kind::Div:       return "div";
        case Kind::Mod:       return "mod";
        case Kind::Abs:       return "abs";
        case Kind::Pow:       return "^";
        case Kind::Eq:        return "=";
        case Kind::Distinct:  return "distinct";
        case Kind::Lt:        return "<";
        case Kind::Leq:       return "<=";
        case Kind::Gt:        return ">";
        case Kind::Geq:       return ">=";
        case Kind::BvNot:     return "bvnot";
        case Kind::BvAnd:     return "bvand";
        case Kind::BvOr:      return "bvor";
        case Kind::BvAdd:     return "bvadd";
        case Kind::BvMul:     return "bvmul";
        case Kind::Forall:    return "forall";
        case Kind::Exists:    return "exists";
        case Kind::ToInt:     return "to_int";
        case Kind::ToReal:    return "to_real";
        case Kind::IsInt:     return "is_int";
        default:              return "";
    }
}

static void dumpRec(ExprId id, const CoreIr& ir, std::ostream& os, int depth = 0) {
    if (depth > 100000) { os << "<DEPTH-LIMIT-EXCEEDED>"; return; }
    if (id >= ir.size()) { os << "???"; return; }
    const auto& e = ir.get(id);

    switch (e.kind) {
        case Kind::ConstBool:
            os << (std::get<bool>(e.payload.value) ? "true" : "false");
            break;
        case Kind::ConstInt:
            os << std::get<int64_t>(e.payload.value);
            break;
        case Kind::ConstReal: {
            const auto& s = std::get<std::string>(e.payload.value);
            os << s;
            break;
        }
        case Kind::ConstBV: {
            if (std::holds_alternative<uint64_t>(e.payload.value)) {
                os << "#b" << std::get<uint64_t>(e.payload.value);
            } else {
                os << std::get<std::string>(e.payload.value);
            }
            break;
        }
        case Kind::ConstFP:
            os << std::get<std::string>(e.payload.value);
            break;
        case Kind::Variable:
            os << std::get<std::string>(e.payload.value);
            break;
        case Kind::UFApply: {
            os << "(" << std::get<std::string>(e.payload.value);
            for (ExprId c : e.children) {
                os << " ";
                dumpRec(c, ir, os, depth + 1);
            }
            os << ")";
            break;
        }
        case Kind::Unknown:
            os << "???";
            break;
        default: {
            const char* op = kindToSMT2(e.kind);
            if (!op || !*op) {
                os << "???";
            } else {
                os << "(" << op;
                for (ExprId c : e.children) {
                    os << " ";
                    dumpRec(c, ir, os, depth + 1);
                }
                os << ")";
            }
            break;
        }
    }
}

std::string dumpExprToSMT2(ExprId id, const CoreIr& ir) {
    std::ostringstream oss;
    dumpRec(id, ir, oss);
    return oss.str();
}

} // namespace nlcolver
