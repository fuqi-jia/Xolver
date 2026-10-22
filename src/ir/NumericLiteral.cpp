#include "ir/NumericLiteral.h"
#include "base/MpqUtils.h"

namespace xolver {
std::optional<mpq_class> numericLiteral(const TermExpr& expr) {
    if (expr.kind != Kind::ConstInt && expr.kind != Kind::ConstReal)
        return std::nullopt;
    try {
        mpq_class value;
        if (const auto* i = std::get_if<int64_t>(&expr.payload.value))
            value = mpqFromString(std::to_string(*i));
        else if (const auto* text = std::get_if<std::string>(&expr.payload.value))
            value = mpqFromString(*text);
        else return std::nullopt;
        if (expr.kind == Kind::ConstInt && value.get_den() != 1) return std::nullopt;
        return value;
    } catch (const std::invalid_argument&) {
        return std::nullopt;
    } catch (const std::out_of_range&) {
        return std::nullopt;
    }
}
std::optional<mpq_class> numericLiteral(const NativeTerms& ir, ExprId id) {
    if (id >= ir.size()) return std::nullopt;
    return numericLiteral(ir.get(id));
}
} // namespace xolver
