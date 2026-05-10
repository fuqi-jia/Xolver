#include "theory/arith/poly/PolynomialConverter.h"
#include "expr/payload.h"
#include <cassert>
#include <gmpxx.h>

namespace nlcolver {

PolyId PolynomialConverter::convert(ExprId eid, const CoreIr& ir) {
    memo_.clear();
    return convertRec(eid, ir);
}

PolyId PolynomialConverter::convertRec(ExprId eid, const CoreIr& ir) {
    auto it = memo_.find(eid);
    if (it != memo_.end()) return it->second;

    const CoreExpr& e = ir.get(eid);
    PolyId result = NullPoly;

    switch (e.kind) {
        case Kind::ConstInt: {
            if (auto* i = std::get_if<int64_t>(&e.payload.value)) {
                result = kernel_.mkConst(mpq_class(*i));
            }
            break;
        }
        case Kind::ConstReal: {
            // ConstReal payload is a string "num/den" or decimal
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                mpq_class q(*s);
                // Phase NRA-1: reject non-integer rational constants to avoid
                // unsoundness from LibPolyKernel::mkConst dropping denominators.
                if (q.get_den() == 1) {
                    result = kernel_.mkConst(q);
                }
            }
            break;
        }
        case Kind::Variable: {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                result = kernel_.mkVar(*s);
            }
            break;
        }
        case Kind::Add: {
            if (e.children.size() >= 2) {
                result = convertRec(e.children[0], ir);
                for (size_t i = 1; i < e.children.size(); ++i) {
                    result = kernel_.add(result, convertRec(e.children[i], ir));
                }
            }
            break;
        }
        case Kind::Sub: {
            if (e.children.size() == 2) {
                result = kernel_.sub(convertRec(e.children[0], ir),
                                     convertRec(e.children[1], ir));
            }
            break;
        }
        case Kind::Neg: {
            if (e.children.size() == 1) {
                result = kernel_.neg(convertRec(e.children[0], ir));
            }
            break;
        }
        case Kind::Mul: {
            if (e.children.size() >= 2) {
                result = convertRec(e.children[0], ir);
                for (size_t i = 1; i < e.children.size(); ++i) {
                    result = kernel_.mul(result, convertRec(e.children[i], ir));
                }
            }
            break;
        }
        case Kind::Pow: {
            if (e.children.size() == 2) {
                PolyId base = convertRec(e.children[0], ir);
                // exponent must be a non-negative integer constant
                const CoreExpr& expNode = ir.get(e.children[1]);
                if (expNode.kind == Kind::ConstInt) {
                    if (auto* i = std::get_if<int64_t>(&expNode.payload.value)) {
                        if (*i >= 0) {
                            result = kernel_.pow(base, static_cast<uint32_t>(*i));
                        }
                    }
                }
            }
            break;
        }
        default:
            // Non-arithmetic or unsupported node
            break;
    }

    memo_[eid] = result;
    return result;
}

} // namespace nlcolver
