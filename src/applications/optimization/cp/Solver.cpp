#include "applications/optimization/cp/Solver.h"
#include "ir/NativeBuilder.h"
#include <somtparser/ir/node.h>
namespace xolver::applications::optimization::cp {
SolverAnswer Solver::solve(const Problem &problem) {
    SolverAnswer answer;
    try {
        if (!decide_) {
            answer.reason = "decision oracle is not attached";
            return answer;
        }
        auto query = problem.constraints;
        native::Nodes nodes(query, workLimit_);
        using K = SOMTParser::NODE_KIND;
        using Node = SOMTParser::Node;
        auto make = [](K kind, std::vector<Node> args) {
            return std::make_shared<SOMTParser::DAGNode>(SOMTParser::SortManager::getBool(), kind,
                                                         SOMTParser::kindToString(kind),
                                                         std::move(args));
        };
        auto compatible = [](Node value, Node variable) {
            if (!value || !value->getSort())
                return false;
            const auto target = variable->getSort(), source = value->getSort();
            // Native numerals may carry the parser's polymorphic arithmetic sort.
            return *source == *target ||
                   (source->isIntOrReal() && value->getKind() == K::NT_CONST &&
                    (target->isInt() || target->isReal()));
        };
        for (const auto &domain : problem.domains) {
            nodes.budget.tick();
            auto variable = domain.variable;
            if (!variable || variable->getKind() != K::NT_VAR || !variable->getSort()) {
                answer.reason = "domain requires a free variable";
                return answer;
            }
            if (domain.kind == Domain::Kind::Enumeration) {
                std::vector<Node> alternatives;
                for (auto value : domain.values) {
                    nodes.budget.tick();
                    if (!compatible(value, variable)) {
                        answer.reason = "domain value sort mismatch";
                        return answer;
                    }
                    alternatives.push_back(make(K::NT_EQ, {variable, value}));
                }
                query.push_back(alternatives.empty() ? make(K::NT_CONST_FALSE, {})
                                                     : make(K::NT_OR, alternatives));
            } else if (domain.kind == Domain::Kind::Interval) {
                if (!(variable->getSort()->isInt() || variable->getSort()->isReal())) {
                    answer.reason = "interval domain requires arithmetic sort";
                    return answer;
                }
                if ((domain.lower && !compatible(domain.lower, variable)) ||
                    (domain.upper && !compatible(domain.upper, variable))) {
                    answer.reason = "interval bound sort mismatch";
                    return answer;
                }
                if (domain.lower)
                    query.push_back(make(K::NT_LE, {domain.lower, variable}));
                if (domain.upper)
                    query.push_back(make(K::NT_LE, {variable, domain.upper}));
            }
        }
        for (const auto &group : problem.allDifferent)
            if (group.size() > 1) {
                for (auto value : group)
                    if (!group[0] || !value || !value->getSort() || !group[0]->getSort() ||
                        *value->getSort() != *group[0]->getSort())
                        throw std::invalid_argument("all-different sort mismatch");
                query.push_back(make(K::NT_DISTINCT, group));
            }
        for (const auto &table : problem.tables) {
            NativeAssertions alternatives;
            for (const auto &tuple : table.tuples) {
                nodes.budget.tick();
                if (tuple.size() != table.variables.size())
                    throw std::invalid_argument("table tuple dimension mismatch");
                NativeAssertions equalities;
                for (std::size_t i = 0; i < tuple.size(); ++i) {
                    if (!table.variables[i] || !table.variables[i]->getSort() ||
                        !compatible(tuple[i], table.variables[i]))
                        throw std::invalid_argument("table tuple sort mismatch");
                    equalities.push_back(nodes.equal(table.variables[i], tuple[i]));
                }
                alternatives.push_back(nodes.all(equalities));
            }
            auto membership = nodes.any(alternatives);
            query.push_back(table.allowed ? membership : nodes.negate(membership));
        }
        for (const auto &element : problem.elements) {
            if (!element.index || !element.index->getSort() || !element.index->getSort()->isInt() ||
                !element.value || !element.value->getSort())
                throw std::invalid_argument("element requires an integer index and a typed result");
            NativeAssertions alternatives;
            for (std::size_t i = 0; i < element.entries.size(); ++i) {
                if (!compatible(element.entries[i], element.value))
                    throw std::invalid_argument("element value sort mismatch");
                mpz_class index = mpz_class(element.indexBase) + mpz_class(i);
                auto numeral =
                    nodes.make(SOMTParser::SortManager::getInt(), K::NT_CONST, {}, index.get_str());
                alternatives.push_back(nodes.all({nodes.equal(element.index, numeral),
                                                  nodes.equal(element.value, element.entries[i])}));
            }
            query.push_back(nodes.any(alternatives));
        }
        for (const auto &cardinality : problem.cardinalities) {
            NativeAssertions values;
            for (auto proposition : cardinality.propositions) {
                if (!proposition || !proposition->getSort() || !proposition->getSort()->isBool())
                    throw std::invalid_argument("cardinality entries must be Boolean");
                values.push_back(nodes.choose(proposition, nodes.numeral(1), nodes.numeral(0)));
            }
            auto sum = values.empty()
                           ? nodes.numeral(0)
                           : nodes.make(SOMTParser::SortManager::getInt(), K::NT_ADD, values);
            if (cardinality.lower)
                query.push_back(nodes.logical(K::NT_GE, {sum, nodes.numeral(*cardinality.lower)}));
            if (cardinality.upper)
                query.push_back(nodes.logical(K::NT_LE, {sum, nodes.numeral(*cardinality.upper)}));
        }
        return decide_(query);
    } catch (const std::exception &e) {
        answer.reason = e.what();
        return answer;
    }
}
} // namespace xolver::applications::optimization::cp
