#pragma once
#include "contracts/IntegerArithmetic.h"
#include "algebra/integer/UnaryArithmetic.h"
#include "base/SolveClock.h"
#include <algorithm>
#include <limits>
#include <set>
#include <stdexcept>

namespace xolver::pa::detail {
struct Stop : std::runtime_error { using std::runtime_error::runtime_error; };
// Exact affine/divisibility algebra. No native DAG, parser, SAT or application
// dependency. The caller supplies a compiler through decide() and shares its
// work budget with projection and model reconstruction.
class IntegerElimination {
protected:
    Limits limits;
    Var nextVariable = 0;
    std::map<Var, std::string> freeNames;
    bool recordSteps;
    EliminationTrace trace_;
    bool recordModel;
    ModelEvidence modelEvidence_;
    std::set<Var> booleanVariables;
    std::set<Var> freeVariables;
    struct Projection { Var variable; Dnf before; };
    std::vector<Projection> projections;
public:
    std::size_t work = 0, eliminated = 0;
    explicit IntegerElimination(Limits l = {}, EvidenceRequest request = {})
        : limits(l), recordSteps(request.elimination), recordModel(request.model) {}
    EliminationTrace takeTrace() { return std::move(trace_); }
    ModelEvidence takeModelEvidence() { return std::move(modelEvidence_); }
    Var fresh() {
        if (nextVariable == std::numeric_limits<Var>::max()) throw Stop("PA variable id overflow");
        return nextVariable++;
    }
    void tick(std::size_t n = 1) {
        if (limits.work && (work >= limits.work || n > limits.work - work))
            throw Stop("PA work budget exhausted");
        work += n;
        if (wall::hasDeadline() && wall::remainingMs() == 0)
            throw Stop("PA wall-clock budget exhausted");
    }
    static bool isTrue(const Dnf& d) { return d.size() == 1 && d.begin()->empty(); }
    // Normalize a conjunction, evaluating constants and tightening integer bounds.
    bool simplify(Cube& cube) {
        Cube kept;
        std::map<std::map<Var, mpz_class>, mpz_class> bounds;
        for (auto& literal : cube) {
            tick();
            auto& a = literal.affine;
            if (literal.divisor != 0) {
                literal.divisor = abs(literal.divisor);
                if (a.coefficients.empty()) {
                    const bool holds = mpz_divisible_p(a.constant.get_mpz_t(),
                                                       literal.divisor.get_mpz_t());
                    if (holds == literal.negatedDivisibility) return false;
                    continue;
                }
                if (literal.divisor == 1) {
                    if (literal.negatedDivisibility) return false;
                    continue;
                }
                mpz_class g = literal.divisor;
                for (const auto& [v, c] : a.coefficients)
                    mpz_gcd(g.get_mpz_t(), g.get_mpz_t(), c.get_mpz_t());
                if (!mpz_divisible_p(a.constant.get_mpz_t(), g.get_mpz_t())) {
                    if (literal.negatedDivisibility) continue;
                    return false;
                }
                if (g > 1) {
                    literal.divisor /= g;
                    a.constant /= g;
                    for (auto& [v, c] : a.coefficients) c /= g;
                }
                mpz_fdiv_r(a.constant.get_mpz_t(), a.constant.get_mpz_t(), literal.divisor.get_mpz_t());
                for (auto it = a.coefficients.begin(); it != a.coefficients.end();) {
                    mpz_fdiv_r(it->second.get_mpz_t(), it->second.get_mpz_t(), literal.divisor.get_mpz_t());
                    if (it->second == 0) it = a.coefficients.erase(it);
                    else ++it;
                }
                if (literal.divisor == 1) {
                    if (literal.negatedDivisibility) return false;
                    continue;
                }
            } else {
                if (a.coefficients.empty()) {
                    if (a.constant > 0) return false;
                    continue;
                }
                mpz_class g = 0;
                for (const auto& [v, c] : a.coefficients)
                    mpz_gcd(g.get_mpz_t(), g.get_mpz_t(), c.get_mpz_t());
                if (g > 1) {
                    for (auto& [v, c] : a.coefficients) c /= g;
                    mpz_cdiv_q(a.constant.get_mpz_t(), a.constant.get_mpz_t(), g.get_mpz_t());
                }
                auto [it, fresh] = bounds.emplace(a.coefficients, a.constant);
                if (!fresh && it->second < a.constant) it->second = a.constant;
                continue;
            }
            kept.push_back(std::move(literal));
        }
        for (const auto& [coefficients, constant] : bounds) {
            auto opposite = coefficients;
            for (auto& [v, c] : opposite) c = -c;
            auto other = bounds.find(opposite);
            if (other != bounds.end() && constant + other->second > 0) return false;
            kept.push_back(Literal{Affine{coefficients, constant}});
        }
        std::sort(kept.begin(), kept.end());
        kept.erase(std::unique(kept.begin(), kept.end(), [](const Literal& a, const Literal& b) {
            return !(a < b) && !(b < a);
        }), kept.end());
        cube = std::move(kept);
        return true;
    }
    void append(Dnf& result, Cube cube) {
        tick(cube.size() + 1);
        if (!simplify(cube) || isTrue(result)) return;
        if (cube.empty()) result = Dnf{Cube{}};
        else result.insert(std::move(cube));
    }
    Dnf atom(Literal l) {
        Dnf result; append(result, Cube{std::move(l)}); return result;
    }
    Dnf either(Dnf a, const Dnf& b) {
        if (isTrue(a) || isTrue(b)) return {Cube{}};
        for (const auto& cube : b) { tick(cube.size() + 1); a.insert(cube); }
        return a;
    }
    Dnf both(const Dnf& a, const Dnf& b) {
        Dnf result;
        for (const auto& ca : a) for (const auto& cb : b) {
            tick(ca.size() + cb.size() + 1);
            Cube cube = ca; cube.insert(cube.end(), cb.begin(), cb.end());
            append(result, std::move(cube));
        }
        return result;
    }
    Dnf negate(const Dnf& d) {
        Dnf result{Cube{}};
        for (const auto& cube : d) {
            Dnf disjunction;
            for (auto l : cube) {
                if (l.divisor != 0) l.negatedDivisibility = !l.negatedDivisibility;
                else { l.affine.multiply(-1); l.affine.constant += 1; }
                disjunction = either(std::move(disjunction), atom(std::move(l)));
            }
            result = both(result, disjunction);
        }
        return result;
    }
    Dnf equal(Affine a, const Affine& b) {
        a.add(b, -1);
        auto result = atom(Literal{a});
        a.multiply(-1);
        return both(result, atom(Literal{std::move(a)}));
    }
    Dnf booleanDomain(Var v) {
        Literal lower; lower.affine.coefficients[v] = -1;
        Literal upper; upper.affine.coefficients[v] = 1; upper.affine.constant = -1;
        return Dnf{Cube{lower, upper}};
    }
    void chargeFormula(const Dnf& formula) {
        for (const auto& cube : formula) {
            tick();
            for (const auto& literal : cube) {
                tick(1 + mpz_size(literal.divisor.get_mpz_t()) +
                     mpz_size(literal.affine.constant.get_mpz_t()));
                for (const auto& [v, c] : literal.affine.coefficients) tick(1 + mpz_size(c.get_mpz_t()));
            }
        }
    }
    Dnf eliminate(const Dnf& input, Var variable) {
        auto output = eliminateImpl(input, variable);
        if (recordSteps) {
            // Copying exact arithmetic obligations consumes the same budget;
            // large integers must not bypass the limit through a cheap copy.
            chargeFormula(input); chargeFormula(output);
            trace_.steps.push_back({variable, input, output});
        }
        return output;
    }
    Cube substitute(const Cube& cube, Var variable, const Affine& witness,
                    bool unboundedBelow = false) {
        Cube substituted;
        for (const auto& l : cube) {
            tick();
            const auto c = l.affine.coefficient(variable);
            if (unboundedBelow && l.divisor == 0 && c != 0) continue;
            Literal next = l;
            next.affine.coefficients.erase(variable);
            next.affine.add(witness, c);
            substituted.push_back(std::move(next));
        }
        return substituted;
    }
    Dnf eliminateImpl(const Dnf& input, Var variable) {
        ++eliminated;
        Dnf result;
        for (auto cube : input) {
            tick(cube.size() + 1);
            mpz_class scale = 1;
            bool occurs = false;
            for (const auto& l : cube) {
                const mpz_class c = l.affine.coefficient(variable);
                if (c != 0) {
                    occurs = true;
                    mpz_lcm(scale.get_mpz_t(), scale.get_mpz_t(), c.get_mpz_t());
                }
            }
            if (!occurs) { append(result, std::move(cube)); continue; }
            // A numeric one-variable conjunction has an exact arithmetic
            // solution without enumerating all residues. Independent literals
            // may still contain other variables: they survive this projection.
            Cube dependent, independent;
            bool univariate = true;
            for (const auto& literal : cube) {
                if (literal.affine.coefficient(variable) == 0)
                    independent.push_back(literal);
                else {
                    if (literal.affine.coefficients.size() != 1) univariate = false;
                    dependent.push_back(literal);
                }
            }
            if (univariate) {
                Assignment values;
                if (witness(dependent, variable, values)) append(result, std::move(independent));
                if (isTrue(result)) return result;
                continue;
            }
            // Rename y = scale*x. Multiplying each atom by a positive integer
            // makes its y coefficient +/-1. scale|y preserves the integer domain.
            for (auto& l : cube) {
                const mpz_class c = l.affine.coefficient(variable);
                if (c == 0) continue;
                mpz_class factor = scale / abs(c);
                l.affine.multiply(factor);
                l.affine.coefficients[variable] = c > 0 ? 1 : -1;
                if (l.divisor != 0) l.divisor *= factor;
            }
            if (scale != 1) {
                Literal constraint;
                constraint.affine.coefficients[variable] = 1;
                constraint.divisor = scale;
                cube.push_back(std::move(constraint));
            }
            // Opposite bounds fix the scaled variable to one affine value.
            // Substitute it once, including in scale|y, instead of enumerating
            // every residue and lower bound. The divisibility condition is
            // essential when the original equality has a non-unit coefficient.
            std::set<Literal> bounds;
            std::optional<Affine> fixed;
            for (const auto& l : cube) {
                const auto c = l.affine.coefficient(variable);
                if (l.divisor != 0 || c == 0) continue;
                tick(l.affine.coefficients.size() + 1);
                auto opposite = l;
                opposite.affine.multiply(-1);
                if (bounds.count(opposite)) {
                    fixed = l.affine;
                    fixed->coefficients.erase(variable);
                    fixed->multiply(-c); // the scaled coefficient is +/-1
                    break;
                }
                bounds.insert(l);
            }
            if (fixed) {
                append(result, substitute(cube, variable, *fixed));
                if (isTrue(result)) return result;
                continue;
            }
            mpz_class period = 1;
            std::vector<Affine> lowerBounds;
            for (const auto& l : cube) {
                const auto c = l.affine.coefficient(variable);
                if (l.divisor != 0 && c != 0)
                    mpz_lcm(period.get_mpz_t(), period.get_mpz_t(), l.divisor.get_mpz_t());
                if (l.divisor == 0 && c == -1) {
                    Affine bound = l.affine;
                    bound.coefficients.erase(variable);
                    lowerBounds.push_back(std::move(bound));
                }
            }
            if (limits.residues && period > mpz_class(limits.residues))
                throw Stop("PA residue budget exhausted");
            // With lower bounds, a satisfying residue has a representative in
            // [max(lower), max(lower)+period-1]. Without them, upper bounds can
            // always be met by moving sufficiently far toward minus infinity.
            const bool unboundedBelow = lowerBounds.empty();
            if (unboundedBelow) lowerBounds.push_back(Affine{});
            for (const auto& lower : lowerBounds) {
                for (mpz_class residue = 0; residue < period; ++residue) {
                    tick();
                    Affine witness = lower; witness.constant += residue;
                    append(result, substitute(cube, variable, witness, unboundedBelow));
                    if (isTrue(result)) return result;
                }
            }
        }
        return result;
    }
    Result close(Dnf result) {
        for (auto v : booleanVariables) result = both(result, booleanDomain(v));
        if (recordModel) { chargeFormula(result); modelEvidence_.formula = result; }
        std::set<Var> free;
        for (const auto& cube : result) for (const auto& l : cube)
            for (const auto& [v, c] : l.affine.coefficients) free.insert(v);
        for (auto it = free.rbegin(); it != free.rend(); ++it) {
            if (!freeVariables.count(*it))
                throw Stop("PA unbound internal variable");
            projections.push_back(Projection{*it, std::move(result)});
            result = eliminate(projections.back().before, *it);
        }
        if (recordSteps) trace_.closed = result;
        if (result.empty()) return Result::Unsat;
        if (isTrue(result)) return Result::Sat;
        throw Stop("PA residual formula did not close");
    }
    using Assignment = std::map<Var, mpz_class>;
    bool holds(const Cube& cube, const Assignment& values) {
        for (const auto& literal : cube) {
            tick();
            mpz_class value = literal.affine.constant;
            for (const auto& [variable, coefficient] : literal.affine.coefficients) {
                auto found = values.find(variable);
                if (found == values.end()) throw Stop("PA incomplete reconstructed model");
                value += coefficient * found->second;
            }
            if (literal.divisor == 0) {
                if (value > 0) return false;
            } else {
                const bool divisible = mpz_divisible_p(value.get_mpz_t(), literal.divisor.get_mpz_t());
                if (divisible == literal.negatedDivisibility) return false;
            }
        }
        return true;
    }
    bool witness(const Cube& cube, Var variable, Assignment& values) {
        Cube numeric;
        for (const auto& literal : cube) {
            tick();
            Literal ground = literal;
            for (const auto& [v, coefficient] : literal.affine.coefficients) {
                if (v == variable) continue;
                auto value = values.find(v);
                if (value == values.end()) throw Stop("PA model projection order mismatch");
                tick(1 + mpz_size(coefficient.get_mpz_t()) + mpz_size(value->second.get_mpz_t()));
                ground.affine.constant += coefficient * value->second;
                ground.affine.coefficients.erase(v);
            }
            numeric.push_back(std::move(ground));
        }
        UnaryArithmetic arithmetic([this](std::size_t amount) { tick(amount); });
        const auto value = arithmetic.solve(numeric, variable);
        if (!value) return false;
        values[variable] = *value;
        if (holds(cube, values)) return true;
        values.erase(variable);
        throw Stop("PA arithmetic witness failed validation");
    }
    std::map<std::string, std::string> model() {
        Assignment values;
        for (auto it = projections.rbegin(); it != projections.rend(); ++it) {
            bool found = false;
            for (const auto& cube : it->before)
                if (witness(cube, it->variable, values)) { found = true; break; }
            if (!found) throw Stop("PA model reconstruction failed");
        }
        // Symbols erased by simplification are unconstrained in the projected
        // formula. In particular, zero is a valid default for a free Boolean.
        for (auto variable : freeVariables) values.try_emplace(variable, 0);
        for (const auto& projection : projections) {
            bool valid = false;
            for (const auto& cube : projection.before)
                if (holds(cube, values)) { valid = true; break; }
            if (!valid) throw Stop("PA reconstructed model failed projection validation");
        }
        std::map<std::string, std::string> result;
        for (auto variable : freeVariables) {
            const auto& name = freeNames.at(variable);
            const auto& value = values.at(variable);
            result[name] = booleanVariables.count(variable)
                ? (value == 0 ? "false" : "true") : value.get_str();
            if (recordModel) {
                tick(name.size() + 1 + mpz_size(value.get_mpz_t()));
                modelEvidence_.symbols.emplace(name, variable);
                if (booleanVariables.count(variable)) modelEvidence_.booleans.insert(variable);
            }
        }
        if (recordModel) modelEvidence_.values = std::move(values);
        return result;
    }
template<class Compile>
Decision decide(Compile compile) {
    Decision result;
    try { result.result = close(compile()); }
    catch (const Stop& error) { result.reason = error.what(); }
    if (result.result == Result::Sat) {
        try {
            result.model = model();
            result.modelAvailable = true;
            if (recordModel) result.modelEvidence = takeModelEvidence();
        } catch (const Stop& error) { result.modelReason = error.what(); }
    }
    if (recordSteps && result.result != Result::Unknown) result.trace = takeTrace();
    result.work = work;
    result.eliminated = eliminated;
    return result;
}
};
} // namespace xolver::pa::detail
