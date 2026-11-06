#include "search/boolean/BooleanDefinitions.h"
#include "ir/NativeTerms.h"
#include <utility>
#include <vector>

namespace xolver {

BooleanPolarities computeBooleanPolarities(std::span<const ExprId> roots,
                                           const NativeTerms& terms) {
    BooleanPolarities result;
    std::vector<std::pair<ExprId, uint8_t>> pending;
    for (const auto root : roots) pending.emplace_back(root, 1);
    auto flipped = [](uint8_t polarity) -> uint8_t {
        return static_cast<uint8_t>(((polarity & 1) << 1) | ((polarity & 2) >> 1));
    };
    while (!pending.empty()) {
        const auto [id, polarity] = pending.back();
        pending.pop_back();
        if (id == NullExpr || id == TrueSentinelExpr || id == FalseSentinelExpr ||
            id >= terms.size()) continue;
        auto& previous = result[id];
        if ((previous & polarity) == polarity) continue;
        previous = static_cast<uint8_t>(previous | polarity);
        const auto& expression = terms.get(id);
        switch (expression.kind) {
            case Kind::Not:
                if (!expression.children.empty())
                    pending.emplace_back(expression.children[0], flipped(polarity));
                break;
            case Kind::And:
            case Kind::Or:
                for (const auto child : expression.children)
                    pending.emplace_back(child, polarity);
                break;
            case Kind::Implies:
                for (size_t i = 0; i < expression.children.size(); ++i)
                    pending.emplace_back(expression.children[i],
                        i + 1 == expression.children.size() ? polarity : flipped(polarity));
                break;
            default:
                // Non-monotone operators and Boolean arguments inside theory
                // terms need both halves of their operands' definitions.
                for (const auto child : expression.children)
                    pending.emplace_back(child, 3);
                break;
        }
    }
    return result;
}

BooleanDefinitionDirections booleanDefinitionDirections(
    const BooleanPolarities& polarities, ExprId expression) {
    const auto found = polarities.find(expression);
    if (found == polarities.end() || found->second == 0) return {};
    return {(found->second & 1) != 0, (found->second & 2) != 0};
}

void emitBooleanNaryDefinition(SatSolver& solver, SatLit output,
                               std::span<const SatLit> inputs, bool conjunction,
                               BooleanDefinitionDirections directions) {
    const bool shortClauses = conjunction ? directions.positive : directions.negative;
    const bool longClause = conjunction ? directions.negative : directions.positive;
    if (shortClauses) {
        for (const auto input : inputs)
            solver.addClause({conjunction ? output.negated() : output,
                              conjunction ? input : input.negated()});
    }
    if (longClause) {
        std::vector<SatLit> clause;
        clause.reserve(inputs.size() + 1);
        clause.push_back(conjunction ? output : output.negated());
        for (const auto input : inputs)
            clause.push_back(conjunction ? input.negated() : input);
        solver.addClause(clause);
    }
}

void emitBooleanIteDefinition(SatSolver& solver, SatLit output,
                              SatLit selector, SatLit thenValue, SatLit elseValue,
                              BooleanDefinitionDirections directions) {
    if (directions.negative)
        solver.addClause({selector.negated(), thenValue.negated(), output});
    if (directions.positive)
        solver.addClause({selector.negated(), thenValue, output.negated()});
    if (directions.negative)
        solver.addClause({selector, elseValue.negated(), output});
    if (directions.positive)
        solver.addClause({selector, elseValue, output.negated()});
}

} // namespace xolver
