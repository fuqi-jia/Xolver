#include "ir/NativeKind.h"

namespace xolver {
using SOMTParser::NODE_KIND;
Kind nativeKind(SOMTParser::NODE_KIND nk) {
    switch (nk) {
        case NODE_KIND::NT_CONST_TRUE:  return Kind::ConstBool;
        case NODE_KIND::NT_CONST_FALSE: return Kind::ConstBool;
        case NODE_KIND::NT_CONST:       return Kind::ConstReal; // refined by payload later
        case NODE_KIND::NT_VAR:         return Kind::Variable;
        case NODE_KIND::NT_QUANT_VAR:   return Kind::BoundVariable;
        case NODE_KIND::NT_UF_APPLY:    return Kind::UFApply;
        case NODE_KIND::NT_FUNC_APPLY:  return Kind::UFApply;
        case NODE_KIND::NT_AND:         return Kind::And;
        case NODE_KIND::NT_OR:          return Kind::Or;
        case NODE_KIND::NT_NOT:         return Kind::Not;
        case NODE_KIND::NT_IMPLIES:     return Kind::Implies;
        case NODE_KIND::NT_XOR:         return Kind::Xor;
        case NODE_KIND::NT_ITE:         return Kind::Ite;
        case NODE_KIND::NT_EQ_BOOL:
        case NODE_KIND::NT_EQ_OTHER:
        case NODE_KIND::NT_EQ:          return Kind::Eq;
        case NODE_KIND::NT_DISTINCT_BOOL:
        case NODE_KIND::NT_DISTINCT_OTHER:
        case NODE_KIND::NT_DISTINCT:    return Kind::Distinct;
        case NODE_KIND::NT_ADD:         return Kind::Add;
        case NODE_KIND::NT_SUB:         return Kind::Sub;
        case NODE_KIND::NT_NEG:         return Kind::Neg;
        case NODE_KIND::NT_MUL:         return Kind::Mul;
        case NODE_KIND::NT_DIV_REAL:
        case NODE_KIND::NT_DIV_INT:     return Kind::Div;
        case NODE_KIND::NT_MOD:         return Kind::Mod;
        case NODE_KIND::NT_ABS:         return Kind::Abs;
        case NODE_KIND::NT_POW:         return Kind::Pow;
        case NODE_KIND::NT_LE:          return Kind::Leq;
        case NODE_KIND::NT_LT:          return Kind::Lt;
        case NODE_KIND::NT_GE:          return Kind::Geq;
        case NODE_KIND::NT_GT:          return Kind::Gt;
        case NODE_KIND::NT_BV_NOT:      return Kind::BvNot;
        case NODE_KIND::NT_BV_AND:      return Kind::BvAnd;
        case NODE_KIND::NT_BV_OR:       return Kind::BvOr;
        case NODE_KIND::NT_BV_ADD:      return Kind::BvAdd;
        case NODE_KIND::NT_BV_MUL:      return Kind::BvMul;
        case NODE_KIND::NT_FORALL:      return Kind::Forall;
        case NODE_KIND::NT_EXISTS:      return Kind::Exists;
        case NODE_KIND::NT_TO_INT:      return Kind::ToInt;
        case NODE_KIND::NT_TO_REAL:     return Kind::ToReal;
        case NODE_KIND::NT_IS_INT:      return Kind::IsInt;
        case NODE_KIND::NT_SELECT:      return Kind::Select;
        case NODE_KIND::NT_STORE:       return Kind::Store;
        case NODE_KIND::NT_CONST_ARRAY: return Kind::ConstArray;
        case NODE_KIND::NT_DT_CONSTRUCTOR: return Kind::Constructor;
        case NODE_KIND::NT_DT_SELECTOR:    return Kind::Selector;
        case NODE_KIND::NT_DT_TESTER:      return Kind::Tester;
        default:                        return Kind::Unknown;
    }
}

}
