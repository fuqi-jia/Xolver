#include "contracts/SeparationModel.h"
#include "contracts/SeparationFormula.h"
#include "base/MpqUtils.h"
#include "evidence/PresburgerModel.h"

namespace xolver::sl {
Evaluation checkInterpretation(const Interpretation& model, Limits limits) {
    try {
        detail::Work work{limits};
        if (model.heap.locationSort != "Int" || model.heap.dataSort != "Int")
            return {false, 0, "unsupported exported heap sorts"};
        std::set<std::string> used;
        for (const auto& [id, value] : model.values) {
            work.tick(value.size() + 1);
            auto integer = rational_detail::integer(value).get_str();
            if (integer != value || !used.insert(value).second)
                return {false, 0, "non-injective or noncanonical integer interpretation"};
        }
        for (const auto& [name, value] : model.assignments) {
            work.tick(name.size() + value.size() + 1);
            if (model.booleans.count(name)) {
                if (value != "true" && value != "false") return {false, work.steps, "invalid Boolean assignment"};
            } else if (rational_detail::integer(value).get_str() != value)
                return {false, work.steps, "noncanonical integer assignment"};
        }
        if (model.heap.nil != model.values.at(0)) return {false, 0, "nil interpretation differs"};
        for (const auto& [id, value] : model.abstract.locations) {
            work.tick(); (void)model.values.at(value);
        }
        for (const auto& [id, literal] : model.literals) {
            work.tick(literal.size() + 1);
            if (model.values.at(model.abstract.locations.at(id)) != literal)
                return {false, 0, "integer literal interpretation differs"};
        }
        for (const auto& [name, id] : model.bindings) {
            work.tick();
            const auto value = model.abstract.locations.at(id);
            const std::string expected = model.booleans.count(name)
                ? (value == 0 ? "true" : "false") : model.values.at(value);
            if (model.assignments.at(name) != expected) return {false, 0, "stack interpretation differs"};
        }
        std::map<std::string, std::string> heap;
        for (const auto& [address, record] : model.abstract.heap) {
            work.tick();
            if (record.size() != 1 || !std::holds_alternative<uint64_t>(record[0]))
                return {false, 0, "invalid exported cell"};
            heap.emplace(model.values.at(address), model.values.at(std::get<uint64_t>(record[0])));
        }
        if (heap != model.heap.cells) return {false, 0, "exported heap differs"};
        if (model.arithmetic) {
            const auto& arithmetic = *model.arithmetic;
            auto checked = pa::checkModel(arithmetic.evidence, limits.maxSteps - work.steps);
            work.tick(checked.steps);
            if (checked.holds != std::optional<bool>(true))
                return {checked.holds, work.steps, checked.reason};
            const auto& evidence = arithmetic.evidence;
            auto value = [&](const std::string& name, bool boolean) {
                const auto variable = evidence.symbols.at(name);
                if (bool(evidence.booleans.count(variable)) != boolean)
                    throw std::invalid_argument("PA/SL model sort mismatch");
                const auto& integer = evidence.values.at(variable);
                return boolean ? std::string(integer == 0 ? "false" : "true") : integer.get_str();
            };
            for (const auto& [id, concrete] : model.abstract.locations) {
                work.tick();
                auto integer = arithmetic.integers.find(id);
                auto predicate = arithmetic.predicates.find(id);
                if ((integer != arithmetic.integers.end()) == (predicate != arithmetic.predicates.end()))
                    return {false, work.steps, "missing or ambiguous PA/SL model binding"};
                if (integer != arithmetic.integers.end()) {
                    if (value(integer->second, false) != model.values.at(concrete))
                        return {false, work.steps, "PA/SL integer interpretations differ"};
                } else if (value(predicate->second, true) != (concrete == 0 ? "true" : "false"))
                    return {false, work.steps, "PA/SL predicate interpretations differ"};
            }
            for (const auto& name : arithmetic.publicSymbols) {
                work.tick();
                if (value(name, model.booleans.count(name)) != model.assignments.at(name))
                    return {false, work.steps, "PA/SL public assignment differs"};
            }
        }
        limits.maxSteps -= work.steps;
        auto result = evaluate(model.query, model.abstract, limits);
        result.steps += work.steps;
        return result;
    } catch (const detail::Stop& e) { return {{}, 0, e.what()};
    } catch (const std::exception& e) { return {false, 0, e.what()}; }
}
} // namespace xolver::sl
