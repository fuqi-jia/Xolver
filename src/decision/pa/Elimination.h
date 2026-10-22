#pragma once
#include "contracts/PresburgerFormula.h"
#include <somtparser/ir/node.h>
#include <unordered_map>
#include <unordered_set>
#include <optional>
#include <limits>
#include "decision/pa/Presburger.h"
#include "decision/pa/UnaryArithmetic.h"
#include "base/MpqUtils.h"
#include "base/SolveClock.h"
#include <gmpxx.h>
#include <algorithm>
#include <map>
#include <set>
#include <stdexcept>
#include <tuple>


namespace xolver::pa::detail {

using SOMTParser::Node;
using K = SOMTParser::NODE_KIND;
struct Stop : std::runtime_error { using std::runtime_error::runtime_error; };

class Engine {
    Limits limits;
    std::size_t nesting = 0;
    Var nextVariable = 0;
    std::unordered_map<Node, Var> variables;
    std::map<Var, std::string> freeNames;
    std::map<std::string, Var> namedVariables;
    bool recordSteps;
    EliminationTrace trace_;
    bool recordModel;
    ModelEvidence modelEvidence_;
    std::set<Var> booleanVariables;
    std::set<Var> freeVariables;
    struct Projection { Var variable; Dnf before; };
    std::vector<Projection> projections;
    struct TermContext {
        Cube guards;
        Dnf definitions{Cube{}};
        std::vector<Var> auxiliaries;
        std::map<std::tuple<Node, bool, std::string>, Var> quotients;
        std::map<Node, Var> piecewise;
    } terms;
public:
    std::size_t work = 0, eliminated = 0;
    explicit Engine(Limits l, EvidenceRequest request)
        : limits(l), recordSteps(request.elimination), recordModel(request.model) {}
    EliminationTrace takeTrace() { return std::move(trace_); }
    ModelEvidence takeModelEvidence() { return std::move(modelEvidence_); }
    Var fresh() {
        if (nextVariable == std::numeric_limits<Var>::max()) throw Stop("PA variable id overflow");
        return nextVariable++;
    }
    Var variable(const Node& n) {
        auto found = variables.find(n);
        if (found != variables.end()) return found->second;
        const Var v = fresh();
        variables.emplace(n, v);
        if (n->getKind() == K::NT_VAR) {
            // A model cannot expose two different symbols under the same name.
            if (!namedVariables.emplace(n->getName(), v).second)
                throw Stop("PA ambiguous free symbol identity");
            freeNames.emplace(v, n->getName());
            freeVariables.insert(v);
            if (n->getSort()->isBool()) booleanVariables.insert(v);
        }
        return v;
    }
    Node resolve(Node n) {
        std::unordered_set<Node> seen;
        while (n) {
            tick();
            const auto k = n->getKind();
            if (k != K::NT_LET && k != K::NT_LET_CHAIN && k != K::NT_LET_BIND_VAR) return n;
            if (!seen.insert(n).second || !n->getChildrenSize()) throw Stop("PA cyclic or empty let alias");
            n = n->getChild(k == K::NT_LET_CHAIN ? n->getChildrenSize() - 1 : 0);
        }
        throw Stop("PA null native term");
    }
    static bool integerSort(const Node& n) {
        return n && n->getSort() && (n->getSort()->isInt() || n->getSort()->isIntOrReal());
    }
    void tick(std::size_t n = 1) {
        if (limits.work && (work >= limits.work || n > limits.work - work))
            throw Stop("PA work budget exhausted");
        work += n;
        if (wall::hasDeadline() && wall::remainingMs() == 0)
            throw Stop("PA wall-clock budget exhausted");
    }
    struct Depth {
        Engine& engine;
        explicit Depth(Engine& e) : engine(e) {
            if (e.limits.depth && e.nesting >= e.limits.depth)
                throw Stop("PA expression depth limit");
            ++e.nesting;
        }
        ~Depth() { --engine.nesting; }
    };
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
    Affine term(Node n) {
        tick(); Depth depth(*this);
        n = resolve(std::move(n));
        const auto kind = n->getKind();
        if (!integerSort(n)) throw Stop("PA requires integer terms");
        Affine value;
        if (kind == K::NT_VAR || kind == K::NT_QUANT_VAR) {
            value.coefficients[variable(n)] = 1; return value;
        }
        if (kind == K::NT_CONST) {
            const auto nativeValue = n->getValue();
            const auto text = nativeValue && nativeValue->getType() == SOMTParser::NUMBER
                ? nativeValue->getNumberValue().toString() : n->getName();
            try {
                const auto number = mpqFromString(text);
                if (number.get_den() != 1) throw Stop("PA non-integral integer literal");
                value.constant = number.get_num();
            } catch (const std::invalid_argument&) { throw Stop("PA invalid integer literal"); }
              catch (const std::out_of_range&) { throw Stop("PA integer literal exponent out of range"); }
            return value;
        }
        if (kind == K::NT_ADD || kind == K::NT_SUB || kind == K::NT_NEG) {
            if (!n->getChildrenSize()) throw Stop("PA missing arithmetic operand");
            for (std::size_t i = 0; i < n->getChildrenSize(); ++i)
                value.add(term(n->getChild(i)),
                          kind == K::NT_NEG || (kind == K::NT_SUB && (i || n->getChildrenSize() == 1)) ? -1 : 1);
            return value;
        }
        if (kind == K::NT_MUL) {
            value.constant = 1;
            for (auto child : SOMTParser::children(n)) {
                auto factor = term(child);
                if (factor.coefficients.empty()) value.multiply(factor.constant);
                else if (value.coefficients.empty()) {
                    factor.multiply(value.constant); value = std::move(factor);
                } else throw Stop("PA nonlinear multiplication");
            }
            return value;
        }
        if ((kind == K::NT_DIV_INT && n->getChildrenSize() >= 2) ||
            (kind == K::NT_MOD && n->getChildrenSize() == 2)) {
            auto dividend = term(n->getChild(0));
            mpz_class modulus = 1;
            bool negative = false;
            // Keep a left-associated chain as s*floor(numerator/modulus).
            // floor(floor(n/m)/d) = floor(n/(m*d)), while
            // floor(-floor(n/m)/d) = floor((-n+m-1)/(m*d)).
            // This needs one quotient witness even for long signed chains.
            for (std::size_t i = 1; i < n->getChildrenSize(); ++i) {
                const auto divisor = term(n->getChild(i));
                if (!divisor.coefficients.empty() || divisor.constant == 0)
                    throw Stop("PA div/mod requires a nonzero constant divisor");
                if (negative) {
                    dividend.multiply(-1);
                    dividend.constant += modulus - 1;
                }
                tick(1 + mpz_size(modulus.get_mpz_t()) + mpz_size(divisor.constant.get_mpz_t()));
                modulus *= abs(divisor.constant);
                negative = divisor.constant < 0;
            }
            const mpz_class divisor = negative ? mpz_class(-modulus) : modulus;
            // Binary div/mod of the same dividend share their exact quotient.
            // A folded n-ary dividend is identified by the entire chain node.
            const auto key = std::tuple{n->getChildrenSize() == 2 ? n->getChild(0) : n,
                                        n->getChildrenSize() != 2, divisor.get_str()};
            auto [it, fresh] = terms.quotients.emplace(key, nextVariable);
            const Var quotient = it->second;
            if (fresh) { this->fresh(); terms.auxiliaries.push_back(quotient); }
            Affine value;
            value.coefficients[quotient] = 1;
            Affine remainder = dividend; remainder.add(value, -divisor);
            if (fresh) {
                Literal nonnegative{remainder}; nonnegative.affine.multiply(-1);
                Literal bounded{remainder}; bounded.affine.constant -= modulus - 1;
                terms.guards.push_back(std::move(nonnegative));
                terms.guards.push_back(std::move(bounded));
            }
            return kind == K::NT_DIV_INT ? value : remainder;
        }
        if ((kind == K::NT_ITE && n->getChildrenSize() == 3) ||
            (kind == K::NT_ABS && n->getChildrenSize() == 1)) {
            if (auto it = terms.piecewise.find(n); it != terms.piecewise.end()) {
                value.coefficients[it->second] = 1;
                return value;
            }
            Dnf condition;
            Affine yes, no;
            if (kind == K::NT_ITE) {
                condition = formula(n->getChild(0));
                yes = term(n->getChild(1));
                no = term(n->getChild(2));
            } else {
                yes = term(n->getChild(0));
                no = yes; no.multiply(-1);
                condition = atom(Literal{no}); // 0 <= argument
            }
            const Var witness = fresh();
            terms.piecewise.emplace(n, witness);
            terms.auxiliaries.push_back(witness);
            value.coefficients[witness] = 1;
            // Both branches define a total, unique integer value. Their
            // definitions may be shared across Boolean connectives, but only
            // within the current quantifier scope.
            auto definition = either(both(condition, equal(value, yes)),
                                     both(negate(condition), equal(value, no)));
            terms.definitions = both(terms.definitions, definition);
            return value;
        }
        throw Stop("PA unsupported arithmetic term");
    }
    Dnf formula(Node n) {
        tick(); Depth depth(*this);
        n = resolve(std::move(n));
        const auto kind = n->getKind();
        if (!n->getSort() || !n->getSort()->isBool()) throw Stop("PA requires Boolean formulas");
        if (kind == K::NT_CONST_TRUE) return Dnf{Cube{}};
        if (kind == K::NT_CONST_FALSE) return Dnf{};
        if (kind == K::NT_CONST) {
            const auto value = n->getValue();
            if (!value || value->getType() != SOMTParser::BOOLEAN)
                throw Stop("PA invalid Boolean literal");
            return value->getBooleanValue() ? Dnf{Cube{}} : Dnf{};
        }
        if (kind == K::NT_VAR || kind == K::NT_QUANT_VAR) {
            Literal positive; positive.affine.coefficients[variable(n)] = -1;
            positive.affine.constant = 1;
            return atom(std::move(positive));
        }
        if (kind == K::NT_NOT && n->getChildrenSize() == 1) return negate(formula(n->getChild(0)));
        if (kind == K::NT_AND || kind == K::NT_OR) {
            Dnf result = kind == K::NT_AND ? Dnf{Cube{}} : Dnf{};
            for (auto c : SOMTParser::children(n)) {
                auto d = formula(c);
                result = kind == K::NT_AND ? both(result, d) : either(std::move(result), d);
            }
            return result;
        }
        if ((kind == K::NT_FORALL || kind == K::NT_EXISTS) && n->getChildrenSize() >= 2) {
            Dnf body = scopedFormula(n->getChild(0));
            for (std::size_t i = n->getChildrenSize(); i-- > 1;) {
                const auto binder = resolve(n->getChild(i));
                const auto sort = binder->getSort();
                if (binder->getKind() != K::NT_QUANT_VAR || !sort ||
                    (!sort->isInt() && !sort->isBool()))
                    throw Stop("PA requires integer or Boolean binders");
                const Var v = variable(binder);
                if (kind == K::NT_FORALL) body = negate(body);
                // forall b:Bool. P is not (exists b:Int. 0<=b<=1 and not P).
                // Restrict the existential counterexample before eliminating;
                // restricting the positive body would quantify all integers.
                if (sort->isBool()) body = both(booleanDomain(v), body);
                body = eliminate(std::move(body), v);
                if (kind == K::NT_FORALL) body = negate(body);
            }
            return body;
        }
        if (kind == K::NT_IMPLIES && n->getChildrenSize() >= 2) {
            auto result = formula(n->getChild(n->getChildrenSize() - 1));
            for (std::size_t i = n->getChildrenSize() - 1; i-- > 0;)
                result = either(negate(formula(n->getChild(i))), result);
            return result;
        }
        if (kind == K::NT_ITE && n->getChildrenSize() == 3) {
            auto condition = formula(n->getChild(0));
            return either(both(condition, formula(n->getChild(1))),
                          both(negate(condition), formula(n->getChild(2))));
        }
        const auto firstSort = n->getChildrenSize() >= 2 ? resolve(n->getChild(0))->getSort() : nullptr;
        const bool booleanEquality = firstSort && firstSort->isBool();
        if (kind == K::NT_XOR) {
            if (n->getChildrenSize() < 2) throw Stop("PA missing xor operand");
            auto result = formula(n->getChild(0));
            for (std::size_t i = 1; i < n->getChildrenSize(); ++i) {
                auto next = formula(n->getChild(i));
                result = either(both(result, negate(next)), both(negate(result), next));
            }
            return result;
        }
        if (kind == K::NT_IS_DIVISIBLE && n->getChildrenSize() == 2) {
            auto dividend = term(n->getChild(0));
            const auto divisor = term(n->getChild(1));
            if (!divisor.coefficients.empty() || divisor.constant <= 0)
                throw Stop("PA divisibility requires a positive constant modulus");
            return atom(Literal{std::move(dividend), divisor.constant});
        }
        if ((kind == K::NT_EQ || kind == K::NT_DISTINCT) && booleanEquality) {
            std::vector<Dnf> operands;
            for (auto child : SOMTParser::children(n)) operands.push_back(formula(child));
            Dnf result{Cube{}};
            for (std::size_t i = 0; i + 1 < operands.size(); ++i) {
                const auto stop = kind == K::NT_DISTINCT ? operands.size() : i + 2;
                for (std::size_t j = i + 1; j < stop; ++j) {
                    auto different = either(both(operands[i], negate(operands[j])),
                                            both(negate(operands[i]), operands[j]));
                    result = both(result, kind == K::NT_EQ ? negate(different) : different);
                }
            }
            return result;
        }
        if (kind != K::NT_EQ && kind != K::NT_DISTINCT && kind != K::NT_LE &&
            kind != K::NT_LT && kind != K::NT_GE && kind != K::NT_GT)
            throw Stop("PA unsupported Boolean term");
        if (n->getChildrenSize() < 2) throw Stop("PA missing comparison operand");
        Dnf result{Cube{}};
        for (std::size_t i = 0; i + 1 < n->getChildrenSize(); ++i) {
            const auto stop = kind == K::NT_DISTINCT ? n->getChildrenSize() : i + 2;
            for (std::size_t j = i + 1; j < stop; ++j) {
                auto difference = term(n->getChild(i));
                difference.add(term(n->getChild(j)), -1);
                if (kind == K::NT_GE || kind == K::NT_GT) difference.multiply(-1);
                Literal first{difference};
                if (kind == K::NT_LT || kind == K::NT_GT) first.affine.constant += 1;
                Dnf relation = atom(first);
                if (kind == K::NT_EQ || kind == K::NT_DISTINCT) {
                    first.affine.multiply(-1);
                    relation = both(relation, atom(first));
                    if (kind == K::NT_DISTINCT) relation = negate(relation);
                }
                result = both(result, relation);
            }
        }
        return result;
    }
    Dnf scopedFormula(Node root) {
        // Quotient and piecewise definitions are total and unique. Share
        // them through Boolean connectives, then existentially close them
        // INSIDE the surrounding binder. Hoisting across forall is unsound.
        auto outer = std::move(terms);
        terms = {};
        auto result = formula(root);
        result = both(Dnf{terms.guards}, result);
        result = both(terms.definitions, result);
        for (auto v : terms.auxiliaries) result = eliminate(std::move(result), v);
        terms = std::move(outer);
        return result;
    }
    Result run(const std::vector<Node>& roots) {
        Dnf result{Cube{}};
        for (auto root : roots) result = both(result, scopedFormula(root));
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
};

inline Decision decide(const std::vector<Node>& roots, Limits limits, EvidenceRequest evidence) {
    Engine engine(limits, evidence);
    Decision result;
    try { result.result = engine.run(roots); }
    catch (const Stop& error) { result.reason = error.what(); }
    if (result.result == Result::Sat) {
        try {
            result.model = engine.model();
            result.modelAvailable = true;
            if (evidence.model) result.modelEvidence = engine.takeModelEvidence();
        } catch (const Stop& error) { result.modelReason = error.what(); }
    }
    if (evidence.elimination && result.result != Result::Unknown) result.trace = engine.takeTrace();
    result.work = engine.work;
    result.eliminated = engine.eliminated;
    return result;
}

}
