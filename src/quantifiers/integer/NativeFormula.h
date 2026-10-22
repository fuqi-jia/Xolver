#pragma once
#include "quantifiers/integer/Elimination.h"
#include "base/MpqUtils.h"
#include <somtparser/ir/node.h>
#include <unordered_map>
#include <unordered_set>

namespace xolver::quantifiers {
// Binder-aware native integer formula compilation. Mathematical projection is
// supplied by IntegerElimination; application selection never happens here.
class IntegerFormula : public pa::detail::IntegerElimination {
    using Node = SOMTParser::Node;
    using K = SOMTParser::NODE_KIND;
    using Var = pa::Var;
    using Affine = pa::Affine;
    using Cube = pa::Cube;
    using Dnf = pa::Dnf;
    using Literal = pa::Literal;
    using Stop = pa::detail::Stop;
    std::size_t nesting = 0;
    std::unordered_map<Node, Var> variables;
    std::map<std::string, Var> namedVariables;
    struct TermContext {
        Cube guards;
        Dnf definitions{Cube{}};
        std::vector<Var> auxiliaries;
        std::map<std::tuple<Node, bool, std::string>, Var> quotients;
        std::map<Node, Var> piecewise;
    } terms;
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
    struct Depth {
        IntegerFormula& engine;
        explicit Depth(IntegerFormula& e) : engine(e) {
            if (e.limits.depth && e.nesting >= e.limits.depth)
                throw Stop("PA expression depth limit");
            ++e.nesting;
        }
        ~Depth() { --engine.nesting; }
    };
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
public:
    using IntegerElimination::IntegerElimination;
    pa::Dnf compile(const std::vector<Node>& roots) {
        Dnf result{Cube{}};
        for (auto root : roots) result = both(result, scopedFormula(root));
        return result;
    }
};
} // namespace xolver::quantifiers
