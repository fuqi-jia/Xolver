#include "applications/sv/sl/NativeArithmetic.h"
#include "applications/sv/sl/HeapSearch.h"
#include "evidence/PresburgerModel.h"
#include <somtparser/ir/node.h>
#include <unordered_set>

namespace xolver::sl::detail {
namespace {
using SOMTParser::Node;
using K = SOMTParser::NODE_KIND;
Node boolean(bool b) {
    return std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getBool(),
        b ? K::NT_CONST_TRUE : K::NT_CONST_FALSE, b ? "true" : "false");
}
Node numeral(const std::string& value) {
    return std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getInt(), K::NT_CONST, value);
}
Node op(K kind, std::vector<Node> args) {
    if (kind == K::NT_AND || kind == K::NT_OR) {
        const bool conjunction = kind == K::NT_AND;
        std::vector<Node> kept;
        for (auto& n : args) {
            if (n->getKind() == (conjunction ? K::NT_CONST_FALSE : K::NT_CONST_TRUE))
                return boolean(!conjunction);
            if (n->getKind() != (conjunction ? K::NT_CONST_TRUE : K::NT_CONST_FALSE))
                kept.push_back(std::move(n));
        }
        if (kept.empty()) return boolean(conjunction);
        if (kept.size() == 1) return kept.front();
        args = std::move(kept);
    }
    return std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getBool(),
        kind, SOMTParser::kindToString(kind), std::move(args));
}
}

NativeArithmetic::NativeArithmetic(Work& w, const std::vector<Node>& roots,
                                   const std::vector<Node>& declarations) : work(w) {
    auto pending = roots;
    pending.insert(pending.end(), declarations.begin(), declarations.end());
    std::unordered_set<Node> visited;
    while (!pending.empty()) {
        work.tick();
        auto n = std::move(pending.back()); pending.pop_back();
        if (!n || !visited.insert(n).second) continue;
        names.insert(n->getName());
        for (auto c : SOMTParser::children(n)) pending.push_back(std::move(c));
    }
    nil = fresh(false);
}
NativeArithmetic::Node NativeArithmetic::fresh(bool b) {
    std::string name;
    do { work.tick(); name = "@xolver.sl." + std::to_string(nextName++); } while (!names.insert(name).second);
    return std::make_shared<SOMTParser::DAGNode>(b ? SOMTParser::SortManager::getBool() :
        SOMTParser::SortManager::getInt(), K::NT_VAR, name);
}
NativeArithmetic::Node NativeArithmetic::pure(Node n, std::size_t depth) {
    work.tick();
    if (!n || depth >= work.limits.maxDepth) throw Stop("SL arithmetic term depth limit");
    if (auto it = rewritten.find(n); it != rewritten.end()) return it->second;
    const auto kind = n->getKind();
    if (kind == K::NT_SEP_NIL) return rewritten.emplace(n, nil).first->second;
    if (kind == K::NT_LET || kind == K::NT_LET_CHAIN || kind == K::NT_LET_BIND_VAR) {
        if (!n->getChildrenSize()) throw Stop("empty SL arithmetic let alias");
        auto value = pure(n->getChild(kind == K::NT_LET_CHAIN ? n->getChildrenSize() - 1 : 0), depth + 1);
        return rewritten.emplace(n, std::move(value)).first->second;
    }
    switch (kind) {
    case K::NT_CONST: case K::NT_CONST_TRUE: case K::NT_CONST_FALSE:
    case K::NT_VAR: case K::NT_QUANT_VAR: case K::NT_FORALL: case K::NT_EXISTS:
    case K::NT_ADD: case K::NT_SUB: case K::NT_NEG: case K::NT_MUL:
    case K::NT_DIV_INT: case K::NT_MOD: case K::NT_ABS: case K::NT_ITE:
    case K::NT_EQ: case K::NT_DISTINCT: case K::NT_LT: case K::NT_LE: case K::NT_GT: case K::NT_GE:
    case K::NT_AND: case K::NT_OR: case K::NT_NOT: case K::NT_IMPLIES: case K::NT_XOR: break;
    default: throw Stop("SL arithmetic must be heap-independent PA");
    }
    if (kind == K::NT_VAR) {
        auto [it, added] = symbols.emplace(n->getName(), n);
        if (!added && it->second != n) throw Stop("ambiguous SL arithmetic symbol identity");
    }
    bool changed = false;
    std::vector<Node> args;
    for (auto c : SOMTParser::children(n)) {
        auto translated = pure(c, depth + 1);
        changed = changed || translated != c;
        args.push_back(std::move(translated));
    }
    auto result = changed ? std::make_shared<SOMTParser::DAGNode>(n->getSort(), kind,
        n->getName(), std::move(args)) : n;
    rewritten.emplace(n, result);
    return result;
}

NativeArithmetic::Node NativeArithmetic::fieldTerm(const Field& value) const {
    return std::holds_alternative<Location>(value) ? integers.at(std::get<Location>(value)) :
        numeral(std::get<std::string>(value));
}

void NativeArithmetic::prepare(const Prepared& p, bool guard) {
    integers.emplace(0, nil);
    constraints.push_back(op(K::NT_EQ, {nil, nil}));
    for (auto id : p.symbols) {
        work.tick();
        if (!id) continue;
        if (auto it = terms.find(id); it != terms.end()) {
            auto variable = fresh(false);
            integers.emplace(id, variable);
            constraints.push_back(op(K::NT_EQ, {variable, pure(it->second)}));
        } else {
            auto variable = fresh(true);
            predicates.emplace(id, variable);
            constraints.push_back(op(K::NT_EQ, {variable, pure(tests.at(id))}));
        }
    }
    if (!guard) return;
    // Necessary stack conditions for truth/falsity. Spatial cases deliberately
    // overapproximate; neither a wand nor a negative star is a pure predicate.
    const auto truth = boolean(true);
    std::vector<std::pair<Node, Node>> conditions(p.formula.nodes.size(), {truth, truth});
    // Addresses that every satisfying (respectively falsifying) heap must
    // allocate. These are necessary conditions only. In particular a wand or
    // a false star need not allocate any particular address in the current heap.
    using Addresses = std::set<Location>;
    std::vector<std::pair<Addresses, Addresses>> allocated(conditions.size());
    using Singleton = std::optional<FormulaId>;
    std::vector<std::pair<Singleton, Singleton>> singletons(conditions.size());
    std::vector<bool> independent(conditions.size(), false);
    auto merge = [&](const Addresses& a, const Addresses& b, bool intersection) {
        Addresses result;
        for (auto id : a) {
            work.tick();
            if (!intersection || b.count(id)) result.insert(id);
        }
        if (!intersection) for (auto id : b) { work.tick(); result.insert(id); }
        return result;
    };
    auto sameHeap = [&](Node condition, Singleton a, Singleton b, const Addresses& addresses) {
        const auto singleton = a ? a : b;
        if (!singleton) return condition;
        const auto& cell = p.formula.nodes[*singleton].cell;
        std::vector<Node> required{condition};
        for (auto address : addresses) {
            work.tick();
            required.push_back(op(K::NT_EQ, {integers.at(cell.address), integers.at(address)}));
        }
        if (a && b) {
            const auto& other = p.formula.nodes[*b].cell;
            if (cell.fields.size() != other.fields.size()) throw Stop("inconsistent SL record arity");
            for (std::size_t i = 0; i < cell.fields.size(); ++i) {
                work.tick();
                required.push_back(op(K::NT_EQ, {fieldTerm(cell.fields[i]), fieldTerm(other.fields[i])}));
            }
        }
        return op(K::NT_AND, std::move(required));
    };
    for (std::size_t i = 0; i < conditions.size(); ++i) {
        if (!p.reachable[i]) continue;
        work.tick();
        const auto& n = p.formula.nodes[i];
        using F = FormulaNode::Kind;
        auto& [yes, no] = conditions[i];
        auto& [yesAllocated, noAllocated] = allocated[i];
        auto& [yesSingleton, noSingleton] = singletons[i];
        if (n.kind == F::Boolean) {
            yes = boolean(n.boolean); no = boolean(!n.boolean); independent[i] = true;
        }
        else if (n.kind == F::Relation) {
            if (auto it = predicates.find(n.relation.left); it != predicates.end()) {
                if (n.relation.right != 0) throw Stop("invalid SL predicate encoding");
                yes = it->second;
            } else yes = op(K::NT_EQ, {integers.at(n.relation.left), integers.at(n.relation.right)});
            if (!n.relation.equal) yes = op(K::NT_NOT, {yes});
            no = op(K::NT_NOT, {yes});
            independent[i] = true;
        } else if (n.kind == F::PointsTo) {
            yes = op(K::NT_NOT, {op(K::NT_EQ, {integers.at(n.cell.address), nil})});
            yesAllocated.insert(n.cell.address);
            yesSingleton = i;
        } else if (n.kind == F::Not) {
            yes = conditions[n.children[0]].second; no = conditions[n.children[0]].first;
            const auto& [a, na] = allocated[n.children[0]];
            yesAllocated = merge(na, {}, false); noAllocated = merge(a, {}, false);
            yesSingleton = singletons[n.children[0]].second;
            noSingleton = singletons[n.children[0]].first;
            independent[i] = independent[n.children[0]];
        } else if (n.kind == F::And || n.kind == F::Or || n.kind == F::Star) {
            const auto& [a, na] = conditions[n.children[0]];
            const auto& [b, nb] = conditions[n.children[1]];
            yes = op(n.kind == F::Or ? K::NT_OR : K::NT_AND, {a, b});
            const auto& [aa, naa] = allocated[n.children[0]];
            const auto& [ab, nab] = allocated[n.children[1]];
            yesAllocated = merge(aa, ab, n.kind == F::Or);
            independent[i] = independent[n.children[0]] && independent[n.children[1]];
            if (n.kind != F::Star) {
                no = op(n.kind == F::Or ? K::NT_AND : K::NT_OR, {na, nb});
                noAllocated = merge(naa, nab, n.kind == F::And);
                const auto& [sa, nsa] = singletons[n.children[0]];
                const auto& [sb, nsb] = singletons[n.children[1]];
                if (n.kind == F::And) {
                    yesSingleton = sa ? sa : sb;
                    noSingleton = nsa == nsb ? nsa : Singleton{};
                    yes = sameHeap(yes, sa, sb, yesAllocated);
                } else {
                    yesSingleton = sa == sb ? sa : Singleton{};
                    noSingleton = nsa ? nsa : nsb;
                    no = sameHeap(no, nsa, nsb, noAllocated);
                }
            } else {
                // Disjoint subheaps cannot allocate the same integer address.
                // Expose that conflict to PA before enumerating unrelated
                // equalities between nil, data values and stack variables.
                std::vector<Node> disjoint{yes};
                for (auto left : aa) for (auto right : ab) {
                    work.tick();
                    disjoint.push_back(op(K::NT_NOT, {op(K::NT_EQ,
                        {integers.at(left), integers.at(right)})}));
                }
                yes = op(K::NT_AND, std::move(disjoint));
                if (independent[i]) no = op(K::NT_OR, {na, nb});
            }
        } else if (n.kind == F::Wand) {
            const auto& [a, na] = conditions[n.children[0]];
            const auto& [b, nb] = conditions[n.children[1]];
            // A false wand has an extension satisfying its antecedent and a
            // union falsifying its consequent. If the antecedent is pure, the
            // empty extension also makes the consequent necessary for truth.
            no = op(K::NT_AND, {a, nb});
            if (independent[n.children[0]]) yes = op(K::NT_OR, {na, b});
            independent[i] = independent[n.children[0]] && independent[n.children[1]];
        }
    }
    constraints.push_back(conditions[p.formula.root].first);
}
pa::Decision NativeArithmetic::decide() {
    work.tick(constraints.size() + 1); // Never pass PA's zero/unlimited sentinel.
    pa::Limits limits;
    limits.work = work.limits.maxSteps - work.steps;
    if (!limits.work) throw Stop("SL arithmetic work limit");
    limits.depth = work.limits.maxDepth;
    quantifiers::IntegerFormula compiler(limits, {.model = true});
    auto result = compiler.decide([&] { return compiler.compile(constraints); });
    work.tick(result.work);
    return result;
}
void NativeArithmetic::reject(const Prepared& prepared, const std::map<Location, uint64_t>& stack) {
    // Construct the blocking clause directly. Building NOT(AND(arrangement))
    // first makes a DNF-based arithmetic solver expand every disequality into
    // two inequalities before negating it: exponentially many intermediate
    // cubes for a clause with only quadratically many observed equalities.
    // Heap truth observes explicit relations, address/nil aliasing, and equality
    // between mentioned records. Cross-equalities of data-only values with
    // addresses are invisible unless a pure relation explicitly mentions them.
    // Fixing these observations preserves the finite heap search's state space
    // and truth values, so an UNSAT result excludes this entire class of stacks.
    std::vector<Node> alternatives;
    std::set<std::pair<Location, Location>> equalities;
    auto equality = [&](Location a, Location b) {
        work.tick();
        if (a == b) return;
        if (b < a) std::swap(a, b);
        if (!equalities.emplace(a, b).second) return;
        auto eq = op(K::NT_EQ, {integers.at(a), integers.at(b)});
        alternatives.push_back(stack.at(a) == stack.at(b) ? op(K::NT_NOT, {eq}) : eq);
    };
    std::vector<const PointsTo*> cells;
    for (std::size_t i = 0; i < prepared.formula.nodes.size(); ++i) {
        if (!prepared.reachable[i]) continue;
        work.tick();
        const auto& n = prepared.formula.nodes[i];
        if (n.kind == FormulaNode::Kind::Relation && !predicates.count(n.relation.left))
            equality(n.relation.left, n.relation.right);
        if (n.kind == FormulaNode::Kind::PointsTo) {
            equality(n.cell.address, 0);
            cells.push_back(&n.cell);
        }
    }
    for (std::size_t i = 0; i < cells.size(); ++i) for (std::size_t j = i + 1; j < cells.size(); ++j) {
        const auto& a = *cells[i];
        const auto& b = *cells[j];
        equality(a.address, b.address);
        work.tick(a.fields.size() + b.fields.size() + 1);
        const bool same = instantiate(a, stack) == instantiate(b, stack);
        if (a.fields.size() != b.fields.size()) throw Stop("inconsistent SL record arity");
        std::vector<Node> fields;
        for (std::size_t k = 0; k < a.fields.size(); ++k) {
            auto eq = op(K::NT_EQ, {fieldTerm(a.fields[k]), fieldTerm(b.fields[k])});
            fields.push_back(same ? op(K::NT_NOT, {eq}) : eq);
        }
        alternatives.push_back(op(same ? K::NT_OR : K::NT_AND, std::move(fields)));
    }
    for (const auto& [id, predicate] : predicates) {
        work.tick();
        alternatives.push_back(stack.at(id) == 0 ? op(K::NT_NOT, {predicate}) : predicate);
    }
    constraints.push_back(op(K::NT_OR, std::move(alternatives)));
}
Outcome NativeArithmetic::solve(const Prepared& p, Interpretation& output) {
    prepare(p, true);
    while (true) {
        auto arithmetic = decide();
        if (arithmetic.result != Result::Sat) return {arithmetic.result, {}, {}, arithmetic.reason};
        if (!arithmetic.modelAvailable || !arithmetic.modelEvidence)
            return {Result::Unknown, {}, {}, "SL requires a PA model: " + arithmetic.modelReason};
        const auto& assignments = arithmetic.model;
        // Nil is an arbitrary mathematical integer, not the numeral zero.
        // Only its abstract equality-class label is fixed to zero.
        std::map<std::string, uint64_t> classes{{assignments.at(nil->getName()), 0}};
        std::map<Location, uint64_t> stack;
        for (const auto& [id, variable] : integers) {
            work.tick();
            auto [it, added] = classes.emplace(assignments.at(variable->getName()), classes.size());
            stack.emplace(id, it->second);
        }
        for (const auto& [id, variable] : predicates) {
            work.tick();
            stack.emplace(id, assignments.at(variable->getName()) == "true" ? 0 : classes.size());
        }
        auto answer = solveHeap(p, stack, work);
        if (answer.result == Result::Sat) {
            output.arithmetic.emplace();
            auto& evidence = *output.arithmetic;
            evidence.evidence = std::move(*arithmetic.modelEvidence);
            for (const auto& [value, id] : classes) output.values.emplace(id, value);
            for (const auto& [id, variable] : integers) evidence.integers.emplace(id, variable->getName());
            for (const auto& [id, variable] : predicates) evidence.predicates.emplace(id, variable->getName());
            for (const auto& [name, variable] : symbols) {
                work.tick();
                const bool b = variable->getSort()->isBool();
                if (b) output.booleans.insert(name);
                const auto it = assignments.find(name);
                output.assignments.emplace(name, it == assignments.end() ? (b ? "false" : "0") : it->second);
                if (it != assignments.end()) evidence.publicSymbols.insert(name);
            }
            return answer;
        }
        if (answer.result != Result::Unsat) return answer;
        reject(p, stack);
    }
}
std::map<Location, uint64_t> NativeArithmetic::evaluate(const Prepared& p,
    const Interpretation& model, const std::function<uint64_t(const std::string&)>& concrete) {
    prepare(p, false);
    constraints.push_back(op(K::NT_EQ, {nil, numeral(model.heap.nil)}));
    for (const auto& [name, variable] : symbols) {
        work.tick();
        const auto& value = model.assignments.at(name);
        Node literal;
        if (variable->getSort()->isBool()) {
            if (value != "true" && value != "false") throw Stop("invalid SL Boolean response binding");
            literal = boolean(value == "true");
        } else literal = numeral(value);
        constraints.push_back(op(K::NT_EQ, {variable, literal}));
    }
    auto answer = decide();
    if (answer.result != Result::Sat || !answer.modelAvailable || !answer.modelEvidence)
        throw Stop("SL arithmetic response could not be evaluated");
    auto checked = pa::checkModel(*answer.modelEvidence, work.limits.maxSteps - work.steps);
    work.tick(checked.steps);
    if (checked.holds != std::optional<bool>(true)) throw Stop("SL arithmetic response model rejected");
    std::map<Location, uint64_t> stack;
    for (const auto& [id, variable] : integers) stack.emplace(id, concrete(answer.model.at(variable->getName())));
    for (const auto& [id, variable] : predicates)
        stack.emplace(id, answer.model.at(variable->getName()) == "true" ? 0 : 1);
    return stack;
}
} // namespace xolver::sl::detail
