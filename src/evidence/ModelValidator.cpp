#include "evidence/ModelValidator.h"
#include "ir/PartialBooleanEvaluation.h"

namespace xolver {
namespace {
PartialBooleanEvaluation assignmentEvaluation(
    const NativeTerms& terms, const ModelValidator::BoolAssignment& assignment) {
    return PartialBooleanEvaluation(terms, [&terms, &assignment](ExprId id) -> std::optional<bool> {
        if (terms.get(id).kind != Kind::Variable) return std::nullopt;
        const auto found = assignment.find(id);
        return found == assignment.end() ? false : found->second;
    });
}
}

bool ModelValidator::validate(const NativeTerms& ir, const BoolAssignment& assignment) {
    auto evaluation = assignmentEvaluation(ir, assignment);
    for (auto root : ir.assertions())
        if (evaluation.evaluate(root) != std::optional<bool>(true)) return false;
    return true;
}

bool ModelValidator::eval(ExprId root, const NativeTerms& ir, const BoolAssignment& assignment) {
    return assignmentEvaluation(ir, assignment).evaluate(root) == std::optional<bool>(true);
}

} // namespace xolver
