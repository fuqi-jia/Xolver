#include "quantifiers/real/Problem.h"
#include "base/MpqUtils.h"
#include <somtparser/ir/node.h>
#include <map>
#include <unordered_map>

namespace xolver::quantifiers::real {
namespace {
using Node = SOMTParser::Node;
using K = SOMTParser::NODE_KIND;
using Poly = RationalPolynomial;
struct Formula { std::vector<Binder> prefix; std::size_t matrix = 1; };
struct Term { Poly polynomial; Formula definitions; };
class Compiler {
    Resources& resources_;
    Problem problem_;
    std::unordered_map<Node, VarId> bound_, free_;
    std::map<std::string, Node> names_;
    std::size_t variables_ = 0;
    static Poly constant(const mpq_class& x) { return Poly::fromConstant(x); }
    static Poly variable(VarId v) { return Poly::fromVar(v, 1, 1); }
    VarId fresh() {
        resources_.tick();
        if (variables_ >= NullVar) throw Exhausted("real variable identifier space exhausted");
        return static_cast<VarId>(variables_++);
    }
    void arity(const Node& n, std::size_t count) {
        if (n->getChildrenSize() != count) throw Unsupported("real operator arity mismatch");
    }
    Node resolve(Node n) {
        std::size_t depth = 0;
        while (n && (n->getKind() == K::NT_LET || n->getKind() == K::NT_LET_BIND_VAR || n->getKind() == K::NT_LET_CHAIN)) {
            resources_.tick();
            if (resources_.limits.depth && ++depth > resources_.limits.depth)
                throw Exhausted("real let expansion depth exhausted");
            if (!n->getChildrenSize()) throw Unsupported("empty real let expression");
            n = n->getChild(n->getKind() == K::NT_LET_CHAIN ? n->getChildrenSize() - 1 : 0);
        }
        if (!n || !n->getSort()) throw Unsupported("invalid real formula node");
        return n;
    }
    VarId symbol(const Node& n) {
        if (n->getKind() == K::NT_QUANT_VAR) {
            const auto found = bound_.find(n);
            if (found == bound_.end()) throw Unsupported("unbound real variable");
            return found->second;
        }
        if (auto found = free_.find(n); found != free_.end()) return found->second;
        if (!names_.emplace(n->getName(), n).second) throw Unsupported("ambiguous real free symbol identity");
        const auto v = fresh();
        free_.emplace(n, v);
        problem_.free.push_back({v, n->getName(), n->getSort()->isBool()});
        return v;
    }
    Formula join(bool conjunction, std::vector<Formula> children) {
        Formula result;
        Connective node{conjunction ? Connective::Kind::And : Connective::Kind::Or, 0, {}};
        bool absorbing = false;
        for (auto& child : children) {
            resources_.tick();
            result.prefix.insert(result.prefix.end(), child.prefix.begin(), child.prefix.end());
            if (child.matrix <= 1) {
                absorbing |= child.matrix == (conjunction ? 0u : 1u);
            } else node.children.push_back(child.matrix);
        }
        if (absorbing || node.children.empty()) result.matrix = absorbing ? !conjunction : conjunction;
        else if (node.children.size() == 1) result.matrix = node.children.front();
        else {
            resources_.nodes(problem_.matrix.size() + 1);
            result.matrix = problem_.matrix.size();
            problem_.matrix.push_back(std::move(node));
        }
        return result;
    }
    Formula atom(Poly polynomial, Relation relation) {
        resources_.tick(polynomial.terms().size() + 1);
        polynomial.normalize();
        if (polynomial.isConstant()) {
            const int s = sgn(polynomial.constantValue());
            const bool holds = relation == Relation::Eq ? s == 0 : relation == Relation::Neq ? s != 0 :
                relation == Relation::Lt ? s < 0 : relation == Relation::Leq ? s <= 0 :
                relation == Relation::Gt ? s > 0 : s >= 0;
            return {{}, holds ? 1u : 0u};
        }
        resources_.nodes(problem_.matrix.size() + 1);
        const auto index = problem_.atoms.size();
        problem_.atoms.push_back({std::move(polynomial), relation});
        const auto id = problem_.matrix.size();
        problem_.matrix.push_back({Connective::Kind::Atom, index, {}});
        return {{}, id};
    }
    Formula domain(VarId v, bool negative) {
        const auto relation = negative ? Relation::Neq : Relation::Eq;
        return join(negative, {atom(variable(v), relation), atom(variable(v) - constant(1), relation)});
    }
    Poly multiply(const Poly& a, const Poly& b) {
        if (b.terms().size() && a.terms().size() > std::numeric_limits<std::size_t>::max() / b.terms().size())
            throw Exhausted("polynomial product exceeds addressable storage");
        resources_.tick(a.terms().size() * b.terms().size() + 1);
        auto result = a * b;
        resources_.nodes(result.terms().size());
        return result;
    }
    Term term(Node n) {
        Resources::Frame frame(resources_);
        n = resolve(std::move(n));
        const auto kind = n->getKind();
        const auto count = n->getChildrenSize();
        if (!n->getSort()->isReal() && !n->getSort()->isInt() && !n->getSort()->isIntOrReal())
            throw Unsupported("real arithmetic requires numeric terms");
        if (kind == K::NT_VAR || kind == K::NT_QUANT_VAR) {
            if (!n->getSort()->isReal()) throw Unsupported("integer variable in real quantifier solver");
            return {variable(symbol(n)), {}};
        }
        if (kind == K::NT_CONST) {
            const auto value = n->getValue();
            const auto text = value && value->getType() == SOMTParser::NUMBER ? value->getNumberValue().toString() : n->getName();
            resources_.tick(text.size());
            return {constant(mpqFromString(text)), {}};
        }
        if (kind == K::NT_TO_REAL) { arity(n, 1); return term(n->getChild(0)); }
        if (kind == K::NT_ADD || kind == K::NT_SUB || kind == K::NT_NEG || kind == K::NT_MUL || kind == K::NT_DIV_REAL) {
            if (!count) throw Unsupported("missing real arithmetic operand");
            if (kind == K::NT_NEG) arity(n, 1);
            if (kind == K::NT_DIV_REAL && count < 2) throw Unsupported("real division requires two operands");
            Term result{constant(kind == K::NT_MUL ? 1 : 0), {}};
            for (std::size_t i = 0; i < count; ++i) {
                auto child = term(n->getChild(i));
                result.definitions = join(true, {std::move(result.definitions), std::move(child.definitions)});
                if (kind == K::NT_MUL) result.polynomial = multiply(result.polynomial, child.polynomial);
                else if (kind == K::NT_DIV_REAL && i > 0) {
                    if (!child.polynomial.isConstant() || child.polynomial.constantValue() == 0)
                        throw Unsupported("polynomial real arithmetic requires nonzero constant divisors");
                    result.polynomial *= mpq_class(1) / child.polynomial.constantValue();
                } else if (kind == K::NT_NEG || (kind == K::NT_SUB && (i > 0 || count == 1)))
                    result.polynomial -= child.polynomial;
                else result.polynomial += child.polynomial;
            }
            return result;
        }
        if (kind == K::NT_POW) {
            arity(n, 2);
            auto base = term(n->getChild(0)), exponent = term(n->getChild(1));
            if (!exponent.polynomial.isConstant()) throw Unsupported("polynomial exponent must be a numeral");
            const auto q = exponent.polynomial.constantValue();
            if (q.get_den() != 1 || q < 0) throw Unsupported("polynomial exponent must be a nonnegative integer");
            if (!q.get_num().fits_uint_p() || q > std::numeric_limits<int>::max())
                throw Exhausted("polynomial exponent exceeds representation budget");
            auto power = q.get_num().get_ui();
            resources_.tick(power);
            Poly result = constant(1), factor = base.polynomial;
            while (power) {
                if (power & 1) result = multiply(result, factor);
                power >>= 1;
                if (power) factor = multiply(factor, factor);
            }
            return {std::move(result), join(true, {std::move(base.definitions), std::move(exponent.definitions)})};
        }
        if (kind == K::NT_ITE || kind == K::NT_ABS) {
            arity(n, kind == K::NT_ITE ? 3 : 1);
            Term yes = term(n->getChild(kind == K::NT_ITE ? 1 : 0));
            Term no = kind == K::NT_ITE ? term(n->getChild(2)) : Term{-yes.polynomial, {}};
            Formula condition = kind == K::NT_ITE ? formula(n->getChild(0), false) : atom(yes.polynomial, Relation::Geq);
            Formula opposite = kind == K::NT_ITE ? formula(n->getChild(0), true) : atom(yes.polynomial, Relation::Lt);
            const auto witness = fresh();
            auto definitions = join(true, {std::move(yes.definitions), std::move(no.definitions),
                join(false, {join(true, {std::move(condition), atom(variable(witness) - yes.polynomial, Relation::Eq)}),
                             join(true, {std::move(opposite), atom(variable(witness) - no.polynomial, Relation::Eq)})})});
            definitions.prefix.insert(definitions.prefix.begin(), {witness, false});
            return {variable(witness), std::move(definitions)};
        }
        throw Unsupported("operator is outside polynomial real arithmetic");
    }
    Formula parity(const Node& node, std::size_t i, bool negative) {
        Resources::Frame frame(resources_);
        if (i == node->getChildrenSize()) return {{}, negative ? 1u : 0u};
        return join(false, {
            join(true, {formula(node->getChild(i), false), parity(node, i + 1, !negative)}),
            join(true, {formula(node->getChild(i), true), parity(node, i + 1, negative)})});
    }
    Formula formula(Node n, bool negative) {
        Resources::Frame frame(resources_);
        n = resolve(std::move(n));
        if (!n->getSort()->isBool()) throw Unsupported("real assertion must be Boolean");
        const auto kind = n->getKind();
        const auto count = n->getChildrenSize();
        if (kind == K::NT_CONST_TRUE || kind == K::NT_CONST_FALSE || kind == K::NT_CONST) {
            bool value = kind == K::NT_CONST_TRUE;
            if (kind == K::NT_CONST) {
                const auto literal = n->getValue();
                if (!literal || literal->getType() != SOMTParser::BOOLEAN) throw Unsupported("invalid Boolean constant");
                value = literal->getBooleanValue();
            }
            return {{}, value != negative ? 1u : 0u};
        }
        if (kind == K::NT_VAR || kind == K::NT_QUANT_VAR)
            return atom(variable(symbol(n)) - constant(1), negative ? Relation::Neq : Relation::Eq);
        if (kind == K::NT_NOT) { arity(n, 1); return formula(n->getChild(0), !negative); }
        if (kind == K::NT_AND || kind == K::NT_OR) {
            std::vector<Formula> children;
            for (auto child : SOMTParser::children(n)) children.push_back(formula(child, negative));
            return join((kind == K::NT_AND) != negative, std::move(children));
        }
        if (kind == K::NT_IMPLIES) {
            if (count < 2) throw Unsupported("implication requires two operands");
            std::vector<Formula> children;
            for (std::size_t i = 0; i < count; ++i)
                children.push_back(formula(n->getChild(i), i + 1 == count ? negative : !negative));
            return join(negative, std::move(children));
        }
        if (kind == K::NT_XOR) return parity(n, 0, negative);
        if (kind == K::NT_ITE) {
            arity(n, 3);
            return join(false, {join(true, {formula(n->getChild(0), false), formula(n->getChild(1), negative)}),
                                join(true, {formula(n->getChild(0), true), formula(n->getChild(2), negative)})});
        }
        if (kind == K::NT_FORALL || kind == K::NT_EXISTS) {
            if (count < 2) throw Unsupported("empty real binder");
            const auto saved = bound_;
            std::vector<Binder> binders;
            std::vector<VarId> booleans;
            const bool universal = (kind == K::NT_FORALL) != negative;
            for (std::size_t i = 1; i < count; ++i) {
                const auto binder = n->getChild(i);
                if (binder->getKind() != K::NT_QUANT_VAR || !binder->getSort() ||
                    (!binder->getSort()->isReal() && !binder->getSort()->isBool()))
                    throw Unsupported("real quantifier requires Real or Bool binders");
                const auto v = fresh();
                bound_[binder] = v;
                binders.push_back({v, universal});
                if (binder->getSort()->isBool()) booleans.push_back(v);
            }
            auto body = formula(n->getChild(0), negative);
            for (auto v : booleans) body = join(!universal, {domain(v, universal), std::move(body)});
            body.prefix.insert(body.prefix.begin(), binders.begin(), binders.end());
            bound_ = saved;
            return body;
        }
        const bool equality = kind == K::NT_EQ || kind == K::NT_EQ_BOOL || kind == K::NT_EQ_OTHER;
        const bool distinct = kind == K::NT_DISTINCT || kind == K::NT_DISTINCT_BOOL || kind == K::NT_DISTINCT_OTHER;
        if (count < 2 || (!equality && !distinct && kind != K::NT_LT && kind != K::NT_LE && kind != K::NT_GT && kind != K::NT_GE))
            throw Unsupported("operator is outside quantified real arithmetic");
        if (n->getChild(0)->getSort()->isBool()) {
            if (!equality && !distinct) throw Unsupported("ordered Boolean comparison");
            std::vector<Formula> comparisons;
            for (std::size_t i = 0; i < count; ++i)
                for (std::size_t j = i + 1; j < count; ++j) {
                    if (equality && i > 0) break;
                    const bool different = distinct != negative;
                    comparisons.push_back(join(false, {
                        join(true, {formula(n->getChild(i), false), formula(n->getChild(j), different)}),
                        join(true, {formula(n->getChild(i), true), formula(n->getChild(j), !different)})}));
                }
            return join(!negative, std::move(comparisons));
        }
        std::vector<Poly> operands;
        std::vector<Formula> definitions, comparisons;
        for (auto child : SOMTParser::children(n)) {
            auto value = term(child);
            operands.push_back(std::move(value.polynomial));
            definitions.push_back(std::move(value.definitions));
        }
        Relation relation = equality ? Relation::Eq : distinct ? Relation::Neq :
            kind == K::NT_LT ? Relation::Lt : kind == K::NT_LE ? Relation::Leq :
            kind == K::NT_GT ? Relation::Gt : Relation::Geq;
        if (negative) relation = relation == Relation::Eq ? Relation::Neq : relation == Relation::Neq ? Relation::Eq :
            relation == Relation::Lt ? Relation::Geq : relation == Relation::Leq ? Relation::Gt :
            relation == Relation::Gt ? Relation::Leq : Relation::Lt;
        for (std::size_t i = 0; i + 1 < count; ++i)
            for (std::size_t j = i + 1; j < count; ++j) {
                comparisons.push_back(atom(operands[i] - operands[j], relation));
                if (!distinct) break;
            }
        definitions.push_back(join(!negative, std::move(comparisons)));
        return join(true, std::move(definitions));
    }
public:
    explicit Compiler(Resources& resources) : resources_(resources) {
        problem_.matrix = {{Connective::Kind::False, 0, {}}, {Connective::Kind::True, 0, {}}};
    }
    Problem run(const Roots& roots) {
        std::vector<Formula> assertions;
        for (const auto& root : roots) assertions.push_back(formula(root, false));
        auto result = join(true, std::move(assertions));
        std::vector<Binder> prefix;
        for (const auto& v : problem_.free) {
            prefix.push_back({v.variable, false});
            if (v.boolean) result = join(true, {domain(v.variable, false), std::move(result)});
        }
        prefix.insert(prefix.end(), result.prefix.begin(), result.prefix.end());
        problem_.prefix = std::move(prefix);
        problem_.root = result.matrix;
        return std::move(problem_);
    }
};
}
Problem compile(const Roots& roots, Resources& resources) {
    return Compiler(resources).run(roots);
}
}
