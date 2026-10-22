#include "evidence/PresburgerModel.h"
#include "base/SolveClock.h"
#include <stdexcept>

namespace xolver::pa {
ModelCheck checkModel(const ModelEvidence& evidence, uint64_t maxSteps) {
    uint64_t steps = 0;
    struct Limit : std::runtime_error { using std::runtime_error::runtime_error; };
    auto tick = [&](uint64_t n = 1) {
        if (n > maxSteps - steps) throw Limit("PA model checking work limit");
        steps += n;
        if (wall::hasDeadline() && wall::remainingMs() == 0)
            throw Limit("PA model checking wall-clock limit");
    };
    auto invalid = [&](const char* reason) { return ModelCheck{false, steps, reason}; };
    try {
        tick();
        std::set<Var> named;
        for (const auto& [name, variable] : evidence.symbols) {
            tick(name.size() + 1);
            if (name.empty() || !named.insert(variable).second || !evidence.values.count(variable))
                return invalid("invalid PA model symbol mapping");
        }
        if (named.size() != evidence.values.size()) return invalid("unnamed PA model value");
        for (auto variable : evidence.booleans) {
            tick();
            auto it = evidence.values.find(variable);
            if (it == evidence.values.end() || (it->second != 0 && it->second != 1))
                return invalid("PA Boolean value outside its domain");
        }
        bool satisfied = false;
        for (const auto& cube : evidence.formula) {
            tick();
            bool conjunction = true;
            for (const auto& literal : cube) {
                tick(1 + mpz_size(literal.divisor.get_mpz_t()) +
                     mpz_size(literal.affine.constant.get_mpz_t()));
                if (literal.divisor < 0 || (literal.divisor == 0 && literal.negatedDivisibility))
                    return invalid("invalid PA model literal");
                mpz_class value = literal.affine.constant;
                for (const auto& [variable, coefficient] : literal.affine.coefficients) {
                    auto it = evidence.values.find(variable);
                    if (it == evidence.values.end()) return invalid("missing PA model value");
                    tick(1 + mpz_size(coefficient.get_mpz_t()) + mpz_size(it->second.get_mpz_t()));
                    value += coefficient * it->second;
                }
                const bool holds = literal.divisor == 0 ? value <= 0 :
                    bool(mpz_divisible_p(value.get_mpz_t(), literal.divisor.get_mpz_t())) !=
                        literal.negatedDivisibility;
                conjunction = conjunction && holds;
            }
            satisfied = satisfied || conjunction;
        }
        return {satisfied, steps, satisfied ? "" : "PA model violates its formula"};
    } catch (const Limit& e) { return {{}, steps, e.what()}; }
}
} // namespace xolver::pa
