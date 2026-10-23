#include "applications/sv/sl/InductiveExpansion.h"
#include "base/MpqUtils.h"
#include <algorithm>
#include <somtparser/ir/node.h>

namespace xolver::sl::detail::inductive {
Node truth(bool value) {
    return std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getBool(),
                                                 value ? K::NT_CONST_TRUE : K::NT_CONST_FALSE,
                                                 value ? "true" : "false");
}
Node operation(K kind, std::vector<Node> children) {
    if (kind == K::NT_AND || kind == K::NT_OR || kind == K::NT_SEP_STAR) {
        const bool disjunction = kind == K::NT_OR;
        std::vector<Node> retained;
        for (const auto &n : children) {
            if (n->getKind() == (disjunction ? K::NT_CONST_TRUE : K::NT_CONST_FALSE))
                return truth(disjunction);
            // true is not an identity for separating conjunction.
            if (kind == K::NT_SEP_STAR ||
                n->getKind() != (disjunction ? K::NT_CONST_FALSE : K::NT_CONST_TRUE))
                if (kind != K::NT_SEP_STAR || n->getKind() != K::NT_SEP_EMP)
                    retained.push_back(n);
        }
        if (retained.empty())
            return kind == K::NT_SEP_STAR ? operation(K::NT_SEP_EMP, {}) : truth(!disjunction);
        if (retained.size() == 1)
            return retained[0];
        children = std::move(retained);
    }
    if (kind == K::NT_NOT && children.size() == 1) {
        if (children[0]->getKind() == K::NT_CONST_FALSE)
            return truth(true);
        if (children[0]->getKind() == K::NT_CONST_TRUE)
            return truth(false);
    }
    return std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getBool(), kind,
                                                 SOMTParser::kindToString(kind),
                                                 std::move(children));
}
void Unfold::depth(std::size_t d) {
    work.tick();
    if (d >= work.limits.maxDepth)
        throw Stop("SL inductive unfolding depth limit");
}

Node Unfold::resolve(Node n) {
    std::size_t d = 0;
    while (n && (n->getKind() == K::NT_LET || n->getKind() == K::NT_LET_CHAIN ||
                 n->getKind() == K::NT_LET_BIND_VAR)) {
        depth(d++);
        if (!n->getChildrenSize())
            throw Stop("empty inductive let alias");
        n = n->getChild(n->getKind() == K::NT_LET_CHAIN ? n->getChildrenSize() - 1 : 0);
    }
    if (!n)
        throw Stop("null inductive term");
    return n;
}

Node Unfold::fresh(const Node &variable, bool free) {
    std::string name;
    do {
        work.tick();
        name = "@xolver.sl.bind." + std::to_string(next++);
    } while (!names.insert(name).second);
    return std::make_shared<SOMTParser::DAGNode>(variable->getSort(),
                                                 free ? K::NT_VAR : K::NT_QUANT_VAR, name);
}

void Unfold::collect(const std::vector<Node> &roots) {
    auto pending = roots;
    std::unordered_set<Node> seen;
    while (!pending.empty()) {
        work.tick();
        auto n = pending.back();
        pending.pop_back();
        if (!n || !seen.insert(n).second)
            continue;
        names.insert(n->getName());
        for (auto c : SOMTParser::children(n))
            pending.push_back(c);
    }
}

bool Unfold::compatible(const Node &actual, const Node &parameter) {
    if (!actual || !parameter)
        return false;
    const auto a = actual->getSort(), b = parameter->getSort();
    return a && b &&
           ((b->isBool() && a->isBool()) || (b->isInt() && (a->isInt() || a->isIntOrReal())));
}

void Unfold::scope(Node n, const std::unordered_set<Node> &parameters,
                   std::unordered_set<Node> binders, std::size_t d) {
    depth(d);
    n = resolve(n);
    const auto kind = n->getKind();
    if (kind == K::NT_FUNC_REC)
        return;
    if (kind == K::NT_FUNC_PARAM && !parameters.count(n))
        throw Stop("unbound inductive function parameter identity");
    if (kind == K::NT_QUANT_VAR && !binders.count(n))
        throw Stop("unbound inductive quantifier variable identity");
    if (kind == K::NT_FORALL || kind == K::NT_EXISTS) {
        if (n->getChildrenSize() < 2)
            throw Stop("malformed inductive quantifier");
        std::unordered_set<Node> local;
        for (std::size_t i = 1; i < n->getChildrenSize(); ++i) {
            auto v = n->getChild(i);
            if (!v || !v->getSort() || v->getKind() != K::NT_QUANT_VAR || !local.insert(v).second ||
                binders.count(v))
                throw Stop("duplicate or invalid inductive quantifier identity");
            binders.insert(v);
        }
        scope(n->getChild(0), parameters, std::move(binders), d + 1);
        return;
    }
    for (auto c : SOMTParser::children(n))
        scope(c, parameters, binders, d + 1);
}
bool Unfold::recursive(Node n, std::size_t d) {
    depth(d);
    n = resolve(n);
    if (n->getKind() == K::NT_FUNC_REC_APPLY)
        return true;
    for (auto c : SOMTParser::children(n))
        if (recursive(c, d + 1))
            return true;
    return false;
}

bool Unfold::heapDependent(Node n, std::size_t d) {
    depth(d);
    n = resolve(n);
    const auto kind = n->getKind();
    if (kind == K::NT_SEP_EMP || kind == K::NT_SEP_PTO || kind == K::NT_SEP_STAR ||
        kind == K::NT_SEP_WAND || kind == K::NT_FUNC_REC_APPLY)
        return true;
    if (kind == K::NT_FUNC_REC)
        return false;
    for (auto child : SOMTParser::children(n))
        if (heapDependent(child, d + 1))
            return true;
    return false;
}

void Unfold::positive(Node n, bool polarity, std::size_t d) {
    depth(d);
    n = resolve(n);
    const auto k = n->getKind();
    const auto count = n->getChildrenSize();
    if (k == K::NT_FUNC_REC_APPLY) {
        const auto &def = definition(n);
        if (!polarity)
            throw Stop(
                "SL inductive definition is not positive; least fixed point is not guaranteed");
        for (std::size_t i = 1; i < count; ++i)
            if (recursive(n->getChild(i), d + 1))
                throw Stop("SL inductive call used in a non-monotone argument");
        return;
    }
    if (k == K::NT_NOT) {
        positive(n->getChild(0), !polarity, d + 1);
        return;
    }
    if (k == K::NT_IMPLIES || k == K::NT_SEP_WAND) {
        if (count < 2)
            throw Stop("malformed inductive connective");
        for (std::size_t i = 0; i < count; ++i)
            positive(n->getChild(i), i + 1 == count ? polarity : !polarity, d + 1);
        return;
    }
    if (k == K::NT_AND || k == K::NT_OR || k == K::NT_SEP_STAR || k == K::NT_FORALL ||
        k == K::NT_EXISTS) {
        const auto end =
            (k == K::NT_FORALL || k == K::NT_EXISTS) ? std::min<std::size_t>(1, count) : count;
        for (std::size_t i = 0; i < end; ++i)
            positive(n->getChild(i), polarity, d + 1);
        return;
    }
    if (k == K::NT_ITE && count == 3 && n->getSort()->isBool() &&
        !recursive(n->getChild(0), d + 1)) {
        positive(n->getChild(1), polarity, d + 1);
        positive(n->getChild(2), polarity, d + 1);
        return;
    }
    if (recursive(n, d + 1))
        throw Stop("SL inductive occurrence is not in a monotone Boolean position");
}

std::optional<mpz_class> Unfold::numeral(const Node &n) {
    if (n->getKind() != K::NT_CONST || !n->getSort() ||
        (!n->getSort()->isInt() && !n->getSort()->isIntOrReal()))
        return {};
    const auto value = n->getValue();
    const auto text = value && value->getType() == SOMTParser::NUMBER
                          ? value->getNumberValue().toString()
                          : n->getName();
    work.tick(text.size() + 1);
    const auto rational = mpqFromString(text);
    if (rational.get_den() != 1)
        return {};
    return rational.get_num();
}

Node Unfold::rebuild(const Node &source, std::vector<Node> args) {
    const auto kind = source->getKind();
    if (kind == K::NT_AND || kind == K::NT_OR || kind == K::NT_NOT || kind == K::NT_SEP_STAR)
        return operation(kind, std::move(args));
    if (kind == K::NT_ITE && args.size() == 3) {
        if (args[0]->getKind() == K::NT_CONST_TRUE)
            return args[1];
        if (args[0]->getKind() == K::NT_CONST_FALSE)
            return args[2];
    }
    if (kind == K::NT_ADD || kind == K::NT_SUB || kind == K::NT_NEG || kind == K::NT_MUL ||
        kind == K::NT_EQ || kind == K::NT_DISTINCT || kind == K::NT_LT || kind == K::NT_LE ||
        kind == K::NT_GT || kind == K::NT_GE) {
        std::vector<mpz_class> values;
        for (const auto &child : args) {
            auto value = numeral(child);
            if (!value) {
                values.clear();
                break;
            }
            values.push_back(*value);
        }
        if (!values.empty() && values.size() == args.size()) {
            if (kind == K::NT_EQ || kind == K::NT_DISTINCT || kind == K::NT_LT ||
                kind == K::NT_LE || kind == K::NT_GT || kind == K::NT_GE) {
                bool holds = true;
                for (std::size_t i = 1; i < values.size(); ++i) {
                    work.tick();
                    if (kind == K::NT_EQ)
                        holds = holds && values[i - 1] == values[i];
                    if (kind == K::NT_LT)
                        holds = holds && values[i - 1] < values[i];
                    if (kind == K::NT_LE)
                        holds = holds && values[i - 1] <= values[i];
                    if (kind == K::NT_GT)
                        holds = holds && values[i - 1] > values[i];
                    if (kind == K::NT_GE)
                        holds = holds && values[i - 1] >= values[i];
                    if (kind == K::NT_DISTINCT)
                        for (std::size_t j = 0; j < i; ++j) {
                            work.tick();
                            holds = holds && values[j] != values[i];
                        }
                }
                return truth(holds);
            }
            mpz_class result = values[0];
            if (kind == K::NT_NEG || (kind == K::NT_SUB && values.size() == 1))
                result = -result;
            else
                for (std::size_t i = 1; i < values.size(); ++i) {
                    work.tick(mpz_sizeinbase(result.get_mpz_t(), 2) +
                              mpz_sizeinbase(values[i].get_mpz_t(), 2));
                    if (kind == K::NT_ADD)
                        result += values[i];
                    else if (kind == K::NT_SUB)
                        result -= values[i];
                    else if (kind == K::NT_MUL)
                        result *= values[i];
                }
            return std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getInt(),
                                                         K::NT_CONST, result.get_str());
        }
    }
    if (args == source->getChildren())
        return source;
    return std::make_shared<SOMTParser::DAGNode>(source->getSort(), kind, source->getName(),
                                                 std::move(args));
}

Node Unfold::substitute(Node n, std::unordered_map<Node, Node> bindings, std::size_t d) {
    depth(d);
    n = resolve(n);
    if (auto it = bindings.find(n); it != bindings.end())
        return it->second;
    const auto k = n->getKind();
    if (k == K::NT_FORALL || k == K::NT_EXISTS) {
        std::vector<Node> binders;
        for (std::size_t i = 1; i < n->getChildrenSize(); ++i) {
            auto old = n->getChild(i), replacement = fresh(old);
            bindings[old] = replacement;
            binders.push_back(replacement);
        }
        std::vector<Node> args{substitute(n->getChild(0), bindings, d + 1)};
        args.insert(args.end(), binders.begin(), binders.end());
        return operation(k, std::move(args));
    }
    // Symbols have immutable identity and must not be cloned.
    if (k == K::NT_FUNC_REC || !n->getChildrenSize())
        return n;
    std::vector<Node> args;
    for (auto c : SOMTParser::children(n))
        args.push_back(substitute(c, bindings, d + 1));
    return rebuild(n, std::move(args));
}

const InductiveDefinition &Unfold::definition(Node n) {
    work.tick();
    if (!n || n->getKind() != K::NT_FUNC_REC_APPLY || !n->getChildrenSize() ||
        !definitions.count(n->getChild(0)))
        throw Stop("unbound SL inductive predicate identity");
    const auto &def = *definitions.at(n->getChild(0));
    if (n->getChildrenSize() != def.parameters.size() + 1)
        throw Stop("SL inductive application arity mismatch");
    for (std::size_t i = 1; i < n->getChildrenSize(); ++i)
        if (!compatible(n->getChild(i), def.parameters[i - 1]))
            throw Stop("SL inductive application sort mismatch");
    return def;
}
Node Unfold::instantiate(Node application, Node body) {
    const auto &def = definition(application);
    std::unordered_map<Node, Node> substitutions;
    std::vector<Node> values, bindings;
    for (std::size_t i = 0; i < def.parameters.size(); ++i) {
        auto actual = application->getChild(i + 1);
        if (heapDependent(actual)) {
            auto value = fresh(def.parameters[i]);
            substitutions.emplace(def.parameters[i], value);
            values.push_back(value);
            bindings.push_back(operation(K::NT_EQ, {value, actual}));
        } else
            substitutions.emplace(def.parameters[i], actual);
    }
    auto instantiated = substitute(body, std::move(substitutions));
    if (values.empty())
        return instantiated;
    bindings.push_back(instantiated);
    std::vector<Node> quantified{operation(K::NT_AND, std::move(bindings))};
    quantified.insert(quantified.end(), values.begin(), values.end());
    return operation(K::NT_EXISTS, std::move(quantified));
}
Node Unfold::formula(Node n, bool lower, std::size_t fuel, std::size_t d) {
    depth(d);
    n = resolve(n);
    const auto k = n->getKind();
    const auto count = n->getChildrenSize();
    if (!recursive(n, d + 1))
        return n;
    if (k == K::NT_FUNC_REC_APPLY) {
        const auto &def = definition(n);
        Node definitionBody = def.body;
        if (!fuel) {
            if (lower)
                return truth(false);
            auto summary = summaries.find(def.symbol);
            if (summary == summaries.end())
                return truth(true);
            definitionBody = summary->second;
        }
        const auto remainingFuel = fuel ? fuel - 1 : 0;
        // Evaluate a conditional actual on the calling heap before the
        // body changes that heap with star/wand. Splitting here preserves
        // this scope and avoids introducing a quantified integer merely
        // to choose between two values.
        for (std::size_t i = 1; i < count; ++i) {
            auto actual = resolve(n->getChild(i));
            if (actual->getKind() != K::NT_ITE || actual->getChildrenSize() != 3 ||
                !heapDependent(actual, d + 1))
                continue;
            auto yes = n->getChildren(), no = yes;
            yes[i] = actual->getChild(1);
            no[i] = actual->getChild(2);
            return formula(
                operation(K::NT_OR,
                          {operation(K::NT_AND, {actual->getChild(0), rebuild(n, std::move(yes))}),
                           operation(K::NT_AND, {operation(K::NT_NOT, {actual->getChild(0)}),
                                                 rebuild(n, std::move(no))})}),
                lower, fuel, d + 1);
        }
        return formula(instantiate(n, definitionBody), lower, remainingFuel, d + 1);
    }
    if (k == K::NT_NOT)
        return operation(k, {formula(n->getChild(0), !lower, fuel, d + 1)});
    if (k == K::NT_IMPLIES || k == K::NT_SEP_WAND) {
        std::vector<Node> args;
        for (std::size_t i = 0; i < count; ++i)
            args.push_back(formula(n->getChild(i), i + 1 == count ? lower : !lower, fuel, d + 1));
        return operation(k, std::move(args));
    }
    if (k == K::NT_AND || k == K::NT_OR || k == K::NT_SEP_STAR) {
        std::vector<Node> args;
        for (auto c : SOMTParser::children(n))
            args.push_back(formula(c, lower, fuel, d + 1));
        return operation(k, std::move(args));
    }
    if (k == K::NT_FORALL || k == K::NT_EXISTS) {
        auto args = n->getChildren();
        args[0] = formula(args[0], lower, fuel, d + 1);
        return operation(k, std::move(args));
    }
    if (k == K::NT_ITE && count == 3 && n->getSort()->isBool()) {
        auto expanded = operation(
            K::NT_OR,
            {operation(K::NT_AND, {n->getChild(0), n->getChild(1)}),
             operation(K::NT_AND, {operation(K::NT_NOT, {n->getChild(0)}), n->getChild(2)})});
        return formula(expanded, lower, fuel, d + 1);
    }
    if ((k == K::NT_EQ || k == K::NT_DISTINCT || k == K::NT_XOR) && count &&
        n->getChild(0)->getSort()->isBool()) {
        auto equivalence = [&](Node a, Node b) {
            return operation(K::NT_OR, {operation(K::NT_AND, {a, b}),
                                        operation(K::NT_AND, {operation(K::NT_NOT, {a}),
                                                              operation(K::NT_NOT, {b})})});
        };
        if (k == K::NT_XOR) {
            auto value = truth(false);
            for (auto c : SOMTParser::children(n))
                value = operation(K::NT_NOT, {equivalence(value, c)});
            return formula(value, lower, fuel, d + 1);
        }
        std::vector<Node> terms;
        for (std::size_t i = 0; i < count; ++i)
            for (std::size_t j = i + 1; j < (k == K::NT_EQ ? std::min(count, i + 2) : count); ++j) {
                auto eq = equivalence(n->getChild(i), n->getChild(j));
                terms.push_back(k == K::NT_EQ ? eq : operation(K::NT_NOT, {eq}));
            }
        return formula(operation(K::NT_AND, std::move(terms)), lower, fuel, d + 1);
    }
    return truth(!lower); // sound enclosing-atom approximation for non-monotone data contexts
}
void prepare(Unfold &unfold, const std::vector<Node> &assertions,
             const std::vector<Node> &declarations,
             const std::vector<InductiveDefinition> &definitions) {
    auto &work = unfold.work;
    unfold.collect(assertions);
    unfold.collect(declarations);
    for (const auto &definition : definitions) {
        work.tick();
        if (!definition.symbol || !definition.body || !definition.body->getSort() ||
            !definition.body->getSort()->isBool() || !definition.symbol->getSort() ||
            !definition.symbol->getSort()->isBool())
            throw Stop("SL inductive predicates must return Bool");
        if (definition.symbol->getKind() != K::NT_FUNC_REC ||
            definition.symbol->getChildrenSize() != definition.parameters.size() + 1 ||
            !definition.symbol->getChild(0) || !definition.symbol->getChild(0)->isNull())
            throw Stop("SL inductive predicate symbol must be an immutable recursive declaration");
        for (std::size_t i = 0; i < definition.parameters.size(); ++i)
            if (!definition.parameters[i] ||
                !Unfold::compatible(definition.symbol->getChild(i + 1), definition.parameters[i]))
                throw Stop("SL inductive declaration/definition parameter sorts differ");
        if (!unfold.definitions.emplace(definition.symbol, &definition).second)
            throw Stop("duplicate inductive predicate identity");
        unfold.collect({definition.body});
        std::unordered_set<Node> parameters;
        for (const auto &parameter : definition.parameters) {
            if (!parameter || parameter->getKind() != K::NT_FUNC_PARAM ||
                !parameters.insert(parameter).second)
                throw Stop("duplicate or invalid SL inductive parameter identity");
            auto sort = parameter->getSort();
            if (!sort || (!sort->isInt() && !sort->isBool()))
                throw Stop("SL inductive parameters require Int/Bool");
        }
        unfold.scope(definition.body, parameters);
    }
    for (const auto &root : assertions) {
        if (!root || !root->getSort() || !root->getSort()->isBool())
            throw Stop("SL assertions must be Boolean");
        unfold.scope(root, {});
    }
    for (const auto &definition : definitions)
        unfold.positive(definition.body);
}
void heapSorts(const std::shared_ptr<SOMTParser::Sort> &location,
               const std::shared_ptr<SOMTParser::Sort> &data) {
    if (!location || !location->isInt() || !data || !data->isInt())
        throw Stop("SL native heap domain currently requires (Int Int)");
}
} // namespace xolver::sl::detail::inductive
