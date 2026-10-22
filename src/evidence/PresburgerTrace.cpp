#include "evidence/PresburgerTrace.h"
#include <nlohmann/json.hpp>
#include <stdexcept>

namespace xolver::pa {
namespace {
nlohmann::json formula(const Dnf& input) {
    auto out = nlohmann::json::array();
    for (const auto& cube : input) {
        auto conjunction = nlohmann::json::array();
        for (const auto& literal : cube) {
            auto coefficients = nlohmann::json::array();
            for (const auto& [v, c] : literal.affine.coefficients)
                coefficients.push_back({std::to_string(v), c.get_str()});
            conjunction.push_back({{"coefficients", coefficients},
                {"constant", literal.affine.constant.get_str()},
                {"divisor", literal.divisor.get_str()},
                {"negated", literal.negatedDivisibility}});
        }
        out.push_back(std::move(conjunction));
    }
    return out;
}
}
std::string serializeTrace(const EliminationTrace& trace, Result result) {
    if (result != Result::Sat && result != Result::Unsat)
        throw std::invalid_argument("incomplete PA decision has no trace certificate");
    auto steps = nlohmann::json::array();
    for (const auto& step : trace.steps)
        steps.push_back({{"variable", std::to_string(step.variable)},
                        {"before", formula(step.before)}, {"after", formula(step.after)}});
    return nlohmann::json{{"schema", "xolver-pa-qe-obligations/1"},
        {"status", "generated-unchecked"},
        {"verdict", result == Result::Sat ? "sat" : "unsat"},
        {"steps", steps}, {"closed", formula(trace.closed)},
        {"step_count", trace.steps.size()}}.dump(2) + "\n";
}
}
