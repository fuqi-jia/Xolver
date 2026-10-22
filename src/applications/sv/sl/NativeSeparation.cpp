#include "applications/sv/sl/NativeSeparation.h"
#include "applications/sv/sl/NativeSpatialSearch.h"
#include "contracts/SeparationFormula.h"
#include "applications/sv/sl/NativeArithmetic.h"
#include "applications/sv/sl/HeapSearch.h"
#include "base/MpqUtils.h"
#include <somtparser/ir/node.h>
#include <limits>
#include <unordered_map>

namespace xolver::sl {
namespace {
using SOMTParser::Node;
using K = SOMTParser::NODE_KIND;
using detail::Stop;

bool integerSort(const std::shared_ptr<SOMTParser::Sort>& sort) {
    return sort && (sort->isInt() || sort->isIntOrReal());
}
std::string integerText(const Node& n) {
    if (!integerSort(n->getSort())) throw Stop("SL expects an integer term");
    const auto value = n->getValue();
    const auto text = value && value->getType() == SOMTParser::NUMBER
        ? value->getNumberValue().toString() : n->getName();
    const auto number = mpqFromString(text);
    if (number.get_den() != 1) throw Stop("non-integral SL literal");
    return number.get_num().get_str();
}
std::string smtInteger(const std::string& value) {
    return !value.empty() && value[0] == '-' ? "(- " + value.substr(1) + ")" : value;
}

struct Import {
    detail::Work work;
    detail::NativeArithmetic arithmetic;
    Formula formula{{FieldSort::Location}};
    Location next = 1;
    std::unordered_map<Node, Location> locations;
    std::unordered_map<Node, FormulaId> formulas;
    std::map<std::string, Location> literals;
    std::map<std::string, Location> bindings;
    std::set<std::string> booleans;

    explicit Import(Limits limits, const std::vector<Node>& roots = {},
                    const std::vector<Node>& declarations = {})
        : work{limits}, arithmetic(work, roots, declarations) {}
    Node resolve(Node n) {
        for (size_t depth = 0; ; ++depth) {
            work.tick();
            if (!n || depth >= work.limits.maxDepth) throw Stop("SL native alias depth limit");
            const auto k = n->getKind();
            if (k != K::NT_LET && k != K::NT_LET_CHAIN && k != K::NT_LET_BIND_VAR) return n;
            if (!n->getChildrenSize()) throw Stop("empty SL let alias");
            n = n->getChild(k == K::NT_LET_CHAIN ? n->getChildrenSize() - 1 : 0);
        }
    }
    Location fresh() {
        work.tick();
        if (next == std::numeric_limits<Location>::max()) throw Stop("SL location id overflow");
        return next++;
    }
    Location literal(const std::string& text) {
        work.tick(text.size());
        auto [it, added] = literals.emplace(text, 0);
        if (added) it->second = fresh();
        return it->second;
    }
    Location location(Node n, size_t depth = 0) {
        n = resolve(std::move(n));
        if (depth >= work.limits.maxDepth) throw Stop("SL native term depth limit");
        if (auto it = locations.find(n); it != locations.end()) return it->second;
        if (!integerSort(n->getSort())) throw Stop("SL location/data sort is not Int");
        Location result;
        switch (n->getKind()) {
        case K::NT_SEP_NIL: result = 0; break;
        case K::NT_VAR:
            result = fresh();
            if (!bindings.emplace(n->getName(), result).second)
                throw Stop("ambiguous native SL symbol identity");
            break;
        case K::NT_CONST: result = literal(integerText(n)); break;
        case K::NT_NEG: {
            if (n->getChildrenSize() != 1) throw Stop("malformed SL integer negation");
            auto child = resolve(n->getChild(0));
            if (child->getKind() == K::NT_CONST) {
                mpz_class value(integerText(child));
                value = -value;
                result = literal(value.get_str());
            } else { result = fresh(); arithmetic.required = true; }
            break;
        }
        default: result = fresh(); arithmetic.required = true; break;
        }
        locations.emplace(n, result);
        arithmetic.integer(result, n);
        return result;
    }
    FormulaId fold(std::vector<FormulaId> ids, K kind) {
        if (ids.empty()) return formula.boolean(kind != K::NT_OR);
        // Balanced construction prevents flat input from creating an artificial
        // recursive depth limit in the SL checker.
        while (ids.size() > 1) {
            std::vector<FormulaId> row;
            for (size_t i = 0; i < ids.size(); i += 2) {
                work.tick();
                if (i + 1 == ids.size()) row.push_back(ids[i]);
                else if (kind == K::NT_AND) row.push_back(formula.conjunction(ids[i], ids[i + 1]));
                else if (kind == K::NT_OR) row.push_back(formula.disjunction(ids[i], ids[i + 1]));
                else row.push_back(formula.star(ids[i], ids[i + 1]));
            }
            ids = std::move(row);
        }
        return ids[0];
    }
    FormulaId equivalent(FormulaId a, FormulaId b) {
        const auto yes = formula.conjunction(a, b);
        const auto na = formula.negate(a), nb = formula.negate(b);
        const auto no = formula.conjunction(na, nb);
        return formula.disjunction(yes, no);
    }
    FormulaId boolean(Node n, size_t depth = 0) {
        n = resolve(std::move(n));
        if (depth >= work.limits.maxDepth) throw Stop("SL native formula depth limit");
        if (auto it = formulas.find(n); it != formulas.end()) return it->second;
        if (!n->getSort() || !n->getSort()->isBool()) throw Stop("non-Boolean SL formula");
        const auto k = n->getKind();
        const auto count = n->getChildrenSize();
        auto child = [&](size_t i) { return boolean(n->getChild(i), depth + 1); };
        auto arity = [&](size_t size) { if (count != size) throw Stop("malformed SL connective arity"); };
        FormulaId result;
        if (k == K::NT_CONST_TRUE || k == K::NT_CONST_FALSE || k == K::NT_CONST) {
            const auto value = n->getValue();
            if (k == K::NT_CONST_TRUE || n->getName() == "true") result = formula.boolean(true);
            else if (k == K::NT_CONST_FALSE || n->getName() == "false") result = formula.boolean(false);
            else if (value && value->getType() == SOMTParser::BOOLEAN)
                result = formula.boolean(value->getBooleanValue());
            else throw Stop("malformed SL Boolean constant");
        } else if (k == K::NT_VAR) {
            const auto id = fresh();
            if (!bindings.emplace(n->getName(), id).second)
                throw Stop("ambiguous native SL Boolean identity");
            booleans.insert(n->getName());
            // A Boolean has two interpretations: equal to nil, or unequal.
            // This auxiliary symbol is never used as a spatial address/data.
            result = formula.relation(id, 0);
            arithmetic.predicate(id, n);
        } else if (k == K::NT_SEP_EMP) {
            arity(0); result = formula.emp();
        } else if (k == K::NT_SEP_PTO) {
            arity(2);
            const auto address = location(n->getChild(0));
            const auto value = location(n->getChild(1));
            result = formula.pointsTo(address, {value});
        } else if (k == K::NT_NOT) {
            arity(1); const auto a = child(0); result = formula.negate(a);
        } else if (k == K::NT_AND || k == K::NT_OR || k == K::NT_SEP_STAR) {
            if (k == K::NT_SEP_STAR && count < 2) throw Stop("malformed SL star arity");
            std::vector<FormulaId> args;
            for (size_t i = 0; i < count; ++i) args.push_back(child(i));
            result = fold(std::move(args), k);
        } else if (k == K::NT_SEP_WAND) {
            arity(2); const auto a = child(0), b = child(1); result = formula.wand(a, b);
        } else if (k == K::NT_IMPLIES) {
            if (count < 2) throw Stop("malformed SL implication");
            result = child(count - 1);
            for (size_t i = count - 1; i-- > 0;) {
                const auto a = child(i), na = formula.negate(a);
                result = formula.disjunction(na, result);
            }
        } else if (k == K::NT_XOR) {
            result = formula.boolean(false);
            for (size_t i = 0; i < count; ++i) {
                const auto a = child(i), eq = equivalent(result, a);
                result = formula.negate(eq);
            }
        } else if (k == K::NT_ITE) {
            arity(3);
            const auto c = child(0), a = child(1), b = child(2);
            const auto nc = formula.negate(c), left = formula.conjunction(c, a);
            const auto right = formula.conjunction(nc, b);
            result = formula.disjunction(left, right);
        } else if (k == K::NT_EQ || k == K::NT_DISTINCT) {
            if (count < 2) throw Stop("malformed SL equality");
            std::vector<FormulaId> pairs;
            for (size_t i = 0; i < count; ++i) {
                const size_t end = k == K::NT_EQ ? std::min(count, i + 2) : count;
                for (size_t j = i + 1; j < end; ++j) {
                    work.tick();
                    auto a = resolve(n->getChild(i)), b = resolve(n->getChild(j));
                    FormulaId eq;
                    if (a->getSort() && a->getSort()->isBool()) {
                        const auto left = boolean(a, depth + 1), right = boolean(b, depth + 1);
                        eq = equivalent(left, right);
                    } else {
                        const auto left = location(a), right = location(b);
                        eq = formula.relation(left, right);
                    }
                    pairs.push_back(k == K::NT_EQ ? eq : formula.negate(eq));
                }
            }
            result = fold(std::move(pairs), K::NT_AND);
        } else if (k == K::NT_LT || k == K::NT_LE || k == K::NT_GT || k == K::NT_GE ||
                   k == K::NT_FORALL || k == K::NT_EXISTS) {
            const auto id = fresh();
            arithmetic.required = true;
            arithmetic.predicate(id, n);
            result = formula.relation(id, 0);
        } else throw Stop("SL quantifiers or inductive predicates are not implemented");
        formulas.emplace(n, result);
        return result;
    }
    Formula query(const std::vector<Node>& assertions) {
        std::vector<FormulaId> roots;
        for (const auto& root : assertions) roots.push_back(boolean(root));
        return finish(std::move(roots));
    }
    Formula valueQuery(const Node& node, std::optional<Location>& integer) {
        if (!integerSort(node->getSort())) return query({node});
        integer = location(node);
        return finish({formula.relation(*integer, *integer)});
    }
    Formula finish(std::vector<FormulaId> roots) {
        // Numeric literals name distinct integers, not freely aliasable locations.
        for (auto a = literals.begin(); a != literals.end(); ++a)
            for (auto b = std::next(a); b != literals.end(); ++b) {
                work.tick();
                roots.push_back(formula.relation(a->second, b->second, false));
            }
        formula.root = fold(std::move(roots), K::NT_AND);
        return std::move(formula);
    }
};

void materialize(Interpretation& out) {
    std::set<std::string> used;
    for (const auto& [id, value] : out.values) used.insert(value);
    for (const auto& [id, literal] : out.literals) {
        const auto value = out.abstract.locations.at(id);
        auto [it, inserted] = out.values.emplace(value, literal);
        if (!inserted && it->second != literal) throw Stop("SL model aliases different integer literals");
        used.insert(literal);
    }
    mpz_class next = 0;
    auto assign = [&](uint64_t value) {
        if (out.values.count(value)) return;
        while (used.count(next.get_str())) ++next;
        auto text = next.get_str();
        out.values.emplace(value, text);
        used.insert(std::move(text)); ++next;
    };
    assign(0);
    for (const auto& [id, value] : out.abstract.locations) assign(value);
    for (const auto& [address, record] : out.abstract.heap) {
        assign(address);
        for (const auto& value : record) assign(std::get<uint64_t>(value));
    }
    out.heap = {"Int", "Int", out.values.at(0), {}};
    for (const auto& [address, record] : out.abstract.heap)
        out.heap.cells.emplace(out.values.at(address), out.values.at(std::get<uint64_t>(record.at(0))));
    for (const auto& [name, id] : out.bindings) {
        const auto value = out.abstract.locations.at(id);
        out.assignments.emplace(name, out.booleans.count(name)
            ? (value == 0 ? "true" : "false") : out.values.at(value));
    }
}
} // namespace

NativeDecision detail::decideGroundNative(const std::shared_ptr<SOMTParser::Sort>& location,
                            const std::shared_ptr<SOMTParser::Sort>& data,
                            const std::vector<Node>& assertions,
                            const std::vector<Node>& declarations, Limits limits) {
    const auto initialWorkLimit = limits.maxSteps;
    try {
        // Int is known infinite. An uninterpreted SMT sort may be finite:
        // applying the infinite-domain wand theorem there can give wrong UNSAT.
        if (!location || !location->isInt() || !data || !data->isInt())
            throw Stop("SL native heap domain currently requires (Int Int)");
        Import importer(limits, assertions, declarations);
        auto model = std::make_shared<Interpretation>();
        model->query = importer.query(assertions);
        for (const auto& [literal, id] : importer.literals) model->literals.emplace(id, literal);
        model->bindings = std::move(importer.bindings);
        model->booleans = std::move(importer.booleans);
        auto prepared = detail::prepare(model->query, importer.work);
        auto result = importer.arithmetic.required
            ? importer.arithmetic.solve(prepared, *model)
            : detail::solveArrangements(prepared, importer.work);
        if (result.result != Result::Sat) return {result.result, result.reason, {}, importer.work.steps};
        model->abstract = std::move(result.model);
        materialize(*model);
        for (const auto& declaration : declarations) {
            if (model->assignments.count(declaration->getName())) continue;
            const auto sort = declaration->getSort();
            if (sort && sort->isBool()) {
                model->booleans.insert(declaration->getName());
                model->assignments.emplace(declaration->getName(), "false");
            } else if (sort && sort->isInt())
                model->assignments.emplace(declaration->getName(), "0");
        }
        limits.maxSteps -= importer.work.steps;
        const auto checked = checkInterpretation(*model, limits);
        if (checked.holds != std::optional<bool>(true))
            return {Result::Unknown, "SL exported model check: " + checked.reason, {}, importer.work.steps + checked.steps};
        return {Result::Sat, {}, std::move(model), importer.work.steps + checked.steps};
    } catch (const std::exception& e) {
        return {Result::Unknown, e.what(), {}, initialWorkLimit};
    }
}

NativeDecision decideNative(const std::shared_ptr<SOMTParser::Sort>& location,
                            const std::shared_ptr<SOMTParser::Sort>& data,
                            const std::vector<Node>& assertions,
                            const std::vector<Node>& declarations, Limits limits) {
    if (!location || !location->isInt() || !data || !data->isInt())
        return {Result::Unknown, "SL native heap domain currently requires (Int Int)", {}, 0};
    try {
        if (detail::hasSpatialBinders(assertions))
            return detail::searchSpatialNative(location, data, assertions, declarations, limits);
        return detail::decideGroundNative(location, data, assertions, declarations, limits);
    } catch (const std::exception& e) { return {Result::Unknown, e.what(), {}, limits.maxSteps}; }
}

void dumpInterpretation(std::ostream& out, const Interpretation& model) {
    out << "(\n";
    for (const auto& [name, value] : model.assignments)
        out << "  (define-fun " << name << " () " << (model.booleans.count(name) ? "Bool " : "Int ")
            << (model.booleans.count(name) ? value : smtInteger(value)) << ")\n";
    out << ")\n(heap\n  ";
    if (model.heap.cells.empty()) out << "sep.emp";
    else {
        if (model.heap.cells.size() > 1) out << "(sep";
        for (const auto& [address, data] : model.heap.cells)
            out << " (pto " << smtInteger(address) << " " << smtInteger(data) << ")";
        if (model.heap.cells.size() > 1) out << ")";
    }
    out << "\n  (= (as sep.nil Int) " << smtInteger(model.heap.nil) << ")\n)\n";
}

std::optional<std::string> nativeValue(const Node& input, const Interpretation& model, Limits limits) {
    try {
        // On a fixed exported heap, keep the source binders and compile their
        // spatial bodies exactly before PA evaluation.
        auto valueInput = detail::hasSpatialBinders({input})
            ? detail::fixedHeapFormula(input, model.heap, limits) : input;
        Import importer(limits, {valueInput});
        const auto node = importer.resolve(valueInput);
        if (node->getKind() == K::NT_SEP_NIL) return smtInteger(model.heap.nil);
        if (node->getKind() == K::NT_VAR) {
            const auto it = model.assignments.find(node->getName());
            if (it == model.assignments.end()) return {};
            return model.booleans.count(it->first) ? it->second : smtInteger(it->second);
        }
        if (node->getKind() == K::NT_CONST && integerSort(node->getSort()))
            return smtInteger(integerText(node));
        // Re-translate Boolean/spatial response terms into the same typed SL
        // language, then evaluate on the existing heap with a fixed stack.
        std::optional<Location> integer;
        auto formula = importer.valueQuery(node, integer);
        Model fixed;
        fixed.heap = model.abstract.heap;
        fixed.locations.emplace(0, 0);
        std::map<std::string, uint64_t> values;
        uint64_t next = 0;
        for (const auto& [id, value] : model.values) {
            values.emplace(value, id);
            if (id == std::numeric_limits<uint64_t>::max()) return {};
            next = std::max(next, id + 1);
        }
        auto concrete = [&](const std::string& value) {
            auto [it, added] = values.emplace(value, next);
            if (added) {
                if (next == std::numeric_limits<uint64_t>::max()) throw Stop("SL response value overflow");
                ++next;
            }
            return it->second;
        };
        if (importer.arithmetic.required) {
            auto prepared = detail::prepare(formula, importer.work);
            fixed.locations = importer.arithmetic.evaluate(prepared, model, concrete);
        } else {
          for (const auto& [literal, id] : importer.literals) fixed.locations[id] = concrete(literal);
          for (const auto& [name, id] : importer.bindings) {
            const auto value = model.assignments.at(name);
            if (importer.booleans.count(name)) {
                // Any existing non-nil representative denotes false.
                if (value != "true" && value != "false") return {};
                fixed.locations[id] = value == "true" ? 0 : 1;
            } else fixed.locations[id] = concrete(value);
          }
        }
        if (integer) {
            const auto id = fixed.locations.at(*integer);
            for (const auto& [text, value] : values) if (value == id) return smtInteger(text);
            return {};
        }
        limits.maxSteps -= importer.work.steps;
        const auto result = evaluate(formula, fixed, limits);
        if (!result.holds) return {};
        return *result.holds ? "true" : "false";
    } catch (const std::exception&) { return {}; }
}
} // namespace xolver::sl
