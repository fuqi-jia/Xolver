#include "xolver/SeparationLogic.h"
#include "evidence/SymbolicHeapChecker.h"
#include "evidence/HeapCertificate.h"
#include "base/IntegerLiteral.h"

namespace xolver::sl {
std::optional<std::pair<Location, Location>> conflictEndpoints(
    const SymbolicHeap& query, const Conflict& conflict) {
    switch (conflict.kind) {
    case Conflict::Kind::PureDisequality:
        if (conflict.first >= query.pure.size() || query.pure[conflict.first].equal) return {};
        return {{query.pure[conflict.first].left, query.pure[conflict.first].right}};
    case Conflict::Kind::NilAllocation:
        if (conflict.first >= query.spatial.size()) return {};
        return {{query.spatial[conflict.first].address, 0}};
    case Conflict::Kind::OverlappingCells:
        if (conflict.first >= query.spatial.size() || conflict.second >= query.spatial.size() ||
            conflict.first == conflict.second) return {};
        return {{query.spatial[conflict.first].address, query.spatial[conflict.second].address}};
    }
    return {};
}

bool checkConflict(const SymbolicHeap& query, const Conflict& conflict) {
    auto pair = conflictEndpoints(query, conflict);
    if (!pair) return false;
    Location current = pair->first;
    for (const auto& step : conflict.path) {
        if (step.premise >= query.pure.size()) return false;
        const auto& premise = query.pure[step.premise];
        if (!premise.equal) return false;
        const Location source = step.reverse ? premise.right : premise.left;
        const Location target = step.reverse ? premise.left : premise.right;
        if (current != source) return false;
        current = target;
    }
    return current == pair->second;
}

bool checkModel(const SymbolicHeap& query, const Model& model) {
    auto nil = model.locations.find(0);
    if (nil == model.locations.end() || nil->second != 0) return false;
    for (const auto& c : query.pure) {
        auto left = model.locations.find(c.left), right = model.locations.find(c.right);
        if (left == model.locations.end() || right == model.locations.end()) return false;
        if ((left->second == right->second) != c.equal) return false;
    }
    std::vector<proof::GroundPointsTo> atoms;
    for (const auto& pto : query.spatial) {
        auto address = model.locations.find(pto.address);
        if (address == model.locations.end()) return false;
        proof::GroundPointsTo atom{{address->second}, {}};
        for (const auto& field : pto.fields) {
            if (auto location = std::get_if<Location>(&field)) {
                auto it = model.locations.find(*location);
                if (it == model.locations.end()) return false;
                atom.record.emplace_back(proof::HeapLocation{it->second});
            } else {
                mpz_class value;
                if (!integerLiteral(std::get<std::string>(field), value)) return false;
                atom.record.emplace_back(std::move(value));
            }
        }
        atoms.push_back(std::move(atom));
    }
    proof::FiniteHeap heap;
    for (const auto& [address, fields] : model.heap) {
        proof::HeapRecord record;
        for (const auto& field : fields) {
            if (auto location = std::get_if<uint64_t>(&field))
                record.emplace_back(proof::HeapLocation{*location});
            else {
                mpz_class value;
                if (!integerLiteral(std::get<std::string>(field), value)) return false;
                record.emplace_back(std::move(value));
            }
        }
        heap.emplace(proof::HeapLocation{address}, std::move(record));
    }
    return proof::checkGroundSymbolicHeap(heap, atoms);
}

} // namespace xolver::sl
