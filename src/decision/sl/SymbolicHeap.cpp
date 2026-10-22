#include "xolver/SeparationLogic.h"
#include "evidence/HeapCertificate.h"
#include "evidence/SymbolicHeapChecker.h"
#include "base/IntegerLiteral.h"
#include <algorithm>
#include <queue>
#include <set>

namespace xolver::sl {
namespace {

}

Outcome solve(const SymbolicHeap& query) {
    // Search uses union-find. The UNSAT checker above only follows a concrete
    // equality path tied to input premises; it does not trust this data structure.
    std::map<Location, Location> parent{{0, 0}};
    auto add = [&](Location v) { parent.emplace(v, v); };
    for (const auto& c : query.pure) { add(c.left); add(c.right); }
    for (const auto& p : query.spatial) {
        add(p.address);
        for (const auto& field : p.fields) {
            if (auto location = std::get_if<Location>(&field)) add(*location);
            else {
                mpz_class value;
                if (!integerLiteral(std::get<std::string>(field), value))
                    return {Result::Unknown, {}, {}, "invalid integer field literal"};
            }
        }
    }
    auto root = [&](Location x) {
        while (parent.at(x) != x) {
            parent[x] = parent.at(parent.at(x));
            x = parent.at(x);
        }
        return x;
    };
    struct Edge { Location target; EqualityStep step; };
    std::map<Location, std::vector<Edge>> edges;
    for (std::size_t i = 0; i < query.pure.size(); ++i) {
        const auto& c = query.pure[i];
        if (!c.equal) continue;
        parent[root(c.left)] = root(c.right);
        edges[c.left].push_back({c.right, {i, false}});
        edges[c.right].push_back({c.left, {i, true}});
    }
    auto refute = [&](Conflict conflict) {
        const auto [source, target] = *conflictEndpoints(query, conflict);
        std::map<Location, std::pair<Location, EqualityStep>> predecessor;
        std::queue<Location> todo;
        predecessor.emplace(source, std::pair{source, EqualityStep{0, false}});
        todo.push(source);
        while (!todo.empty() && !predecessor.count(target)) {
            const auto at = todo.front(); todo.pop();
            for (const auto& edge : edges[at]) {
                if (predecessor.emplace(edge.target, std::pair{at, edge.step}).second)
                    todo.push(edge.target);
            }
        }
        for (Location at = target; at != source;) {
            auto it = predecessor.find(at);
            if (it == predecessor.end())
                return Outcome{Result::Unknown, {}, {}, "location proof reconstruction failed"};
            conflict.path.push_back(it->second.second);
            at = it->second.first;
        }
        std::reverse(conflict.path.begin(), conflict.path.end());
        if (!checkConflict(query, conflict))
            return Outcome{Result::Unknown, {}, {}, "location conflict certificate rejected"};
        return Outcome{Result::Unsat, {}, std::move(conflict), {}};
    };
    for (std::size_t i = 0; i < query.pure.size(); ++i) {
        const auto& c = query.pure[i];
        if (!c.equal && root(c.left) == root(c.right))
            return refute({Conflict::Kind::PureDisequality, i, 0, {}});
    }
    std::map<Location, std::size_t> allocated;
    for (std::size_t i = 0; i < query.spatial.size(); ++i) {
        const auto address = root(query.spatial[i].address);
        if (address == root(0)) return refute({Conflict::Kind::NilAllocation, i, 0, {}});
        auto [it, fresh] = allocated.emplace(address, i);
        if (!fresh) return refute({Conflict::Kind::OverlappingCells, it->second, i, {}});
    }
    Outcome outcome;
    std::map<Location, uint64_t> values{{root(0), 0}};
    uint64_t next = 1;
    for (const auto& [variable, ignored] : parent) {
        const auto representative = root(variable);
        auto it = values.find(representative);
        if (it == values.end()) it = values.emplace(representative, next++).first;
        outcome.model.locations.emplace(variable, it->second);
    }
    for (const auto& atom : query.spatial) {
        std::vector<ConcreteField> record;
        for (const auto& field : atom.fields) {
            if (auto location = std::get_if<Location>(&field))
                record.emplace_back(outcome.model.locations.at(*location));
            else {
                mpz_class value; integerLiteral(std::get<std::string>(field), value);
                record.emplace_back(value.get_str());
            }
        }
        outcome.model.heap.emplace(outcome.model.locations.at(atom.address), std::move(record));
    }
    if (checkModel(query, outcome.model)) outcome.result = Result::Sat;
    else outcome.reason = "constructed heap witness rejected";
    return outcome;
}
} // namespace xolver::sl
