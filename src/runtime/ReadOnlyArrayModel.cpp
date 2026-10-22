#include "runtime/SolverImpl.h"
#include <algorithm>

namespace xolver {

bool Solver::Impl::reconstructReadOnlyArrays() {
    if (roaeReads_.empty()) return true;
    if (!ir || !lastModel_) return false;
    auto candidate = *lastModel_;

    // Extend unconstrained scalar witnesses consistently. Only variables used
    // by the eliminated reads need completion; assigned values are preserved.
    std::vector<ExprId> pending;
    for (const auto& read : roaeReads_) {
        pending.push_back(read.arrOperand);
        pending.push_back(read.idxExpr);
        pending.push_back(read.freshVar);
    }
    std::unordered_set<ExprId> seen;
    while (!pending.empty()) {
        const auto id = pending.back(); pending.pop_back();
        if (!seen.insert(id).second) continue;
        const auto term = ir->get(id);
        pending.insert(pending.end(), term.children.begin(), term.children.end());
        if (term.kind != Kind::Variable || ir->arraySortParams(term.sort)) continue;
        const auto name = std::get_if<std::string>(&term.payload.value);
        if (!name || candidate.assignments.count(*name) ||
            candidate.numericAssignments.count(*name)) continue;
        const auto kind = ir->sortKind(term.sort);
        if (kind == SortKind::Int || kind == SortKind::Real) {
            candidate.assignments.emplace(*name, "0");
            candidate.numericAssignments.emplace(*name, RealValue::fromInt(0));
        } else if (kind == SortKind::Bool) {
            candidate.assignments.emplace(*name, "false");
        } else {
            candidate.assignments.emplace(*name, "@roae-default:" +
                ir->native(id)->getSort()->toString());
        }
    }

    ArithModelValidator::NumAssignment numbers;
    ArithModelValidator::BoolAssignment booleans;
    for (const auto& [name, value] : candidate.assignments) {
        if (value == "true" || value == "false") booleans[name] = value == "true";
        else {
            try {
                mpq_class q(value.rfind("#n:", 0) == 0 ? value.substr(3) : value);
                if (q.get_den() == 0) return false;
                q.canonicalize();
                numbers[name] = q;
            } catch (const std::invalid_argument&) {}
        }
    }
    for (const auto& [name, value] : candidate.numericAssignments)
        if (auto q = value.tryAsRational()) numbers[name] = *q;
    ArithModelValidator eval(*ir, numbers, booleans, candidate.arrayInterps,
                             candidate.assignments);
    eval.setRealAssignments(&candidate.numericAssignments);
    eval.setFunctionInterps(&candidate.functionInterps, &candidate.arrayValues);

    using NativeSort = std::shared_ptr<SOMTParser::Sort>;
    using Array = TheoryModel::ArrayInterp;
    std::size_t nextHandle = 0;
    auto saveArray = [&](Array array) {
        std::string handle;
        do { handle = "@roae-array!" + std::to_string(nextHandle++); }
        while (candidate.arrayValues.count(handle));
        candidate.arrayValues.emplace(handle, std::move(array));
        return handle;
    };
    std::function<std::string(const NativeSort&)> defaultValue;
    auto emptyArray = [&](const NativeSort& sort) -> Array {
        const auto index = sort->getIndexSort(), elem = sort->getElemSort();
        return {index->toString(), elem->toString(), defaultValue(elem), {}};
    };
    defaultValue = [&](const NativeSort& sort) -> std::string {
        if (sort->isArray()) return saveArray(emptyArray(sort));
        const auto name = sort->toString();
        if (name == "Int" || name == "Real") return "#n:0";
        if (name == "Bool") return "#b:0";
        return "@roae-default:" + name;
    };

    // A trie of concrete index paths shares equal prefixes even when the source
    // indices were syntactically different. Reject conflicting leaves instead
    // of silently choosing the first/last read at a coinciding index.
    std::function<bool(Array&, const NativeSort&, const std::vector<std::string>&,
                       std::size_t, const std::string&)> insert;
    insert = [&](Array& array, const NativeSort& sort,
                 const std::vector<std::string>& path, std::size_t pos,
                 const std::string& value) {
        auto entry = std::find_if(array.entries.begin(), array.entries.end(),
            [&](const auto& item) { return item.first == path[pos]; });
        if (pos + 1 == path.size()) {
            if (entry != array.entries.end()) return entry->second == value;
            array.entries.emplace_back(path[pos], value);
            return true;
        }
        const auto innerSort = sort->getElemSort();
        if (!innerSort || !innerSort->isArray()) return false;
        std::string child;
        if (entry == array.entries.end()) {
            child = saveArray(emptyArray(innerSort));
            array.entries.emplace_back(path[pos], child);
        } else child = entry->second;
        return insert(candidate.arrayValues.at(child), innerSort, path, pos + 1, value);
    };

    std::unordered_set<std::string> rebuilt;
    for (const auto& read : roaeReads_) {
        std::vector<ExprId> indices{read.idxExpr};
        auto base = read.arrOperand;
        auto term = ir->get(base);
        while (term.kind == Kind::Select && term.children.size() == 2) {
            indices.push_back(term.children[1]);
            base = term.children[0];
            term = ir->get(base);
        }
        if (term.kind != Kind::Variable) return false;
        const auto name = std::get_if<std::string>(&term.payload.value);
        if (!name) return false;
        std::reverse(indices.begin(), indices.end());
        std::vector<std::string> path;
        for (const auto index : indices) {
            const auto value = eval.evalToken(index);
            if (!value) return false;
            path.push_back(*value);
        }
        const auto value = eval.evalToken(read.freshVar);
        if (!value) return false;
        const auto sort = ir->native(base)->getSort();
        if (rebuilt.insert(*name).second) candidate.arrayInterps[*name] = emptyArray(sort);
        if (!insert(candidate.arrayInterps.at(*name), sort, path, 0, *value)) return false;
    }
    // Certify exactly the interpretation exported by get-model and checked by
    // the public API, with no read overrides that could mask a broken table.
    if (eval.validate(originalAssertions_) != ArithModelValidator::Verdict::Satisfied)
        return false;
    *lastModel_ = std::move(candidate);
    return true;
}

} // namespace xolver
