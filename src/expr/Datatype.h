#pragma once

#include "expr/types.h"
#include <string>
#include <vector>
#include <unordered_map>

namespace xolver {

// ---------------------------------------------------------------------------
// DatatypeRegistry — Xolver-native algebraic-datatype signature.
//
// Populated by the FrontendAdapter from SOMTParser's declare-datatypes
// metadata, translated entirely into Xolver SortIds so that CoreIr (the DAG
// view) and the theory layer never include heavy parser headers. One entry
// per datatype sort: an ordered list of constructors, each with an ordered
// list of selectors (name + result sort). Testers are derived from the
// constructor list (one tester per constructor).
//
// All DT operator nodes (Kind::Constructor / Selector / Tester) carry their
// operator NAME in the CoreExpr payload string; this registry resolves a name
// (in the context of the datatype sort) back to a constructor index / field
// position, which is what the DtReasoner needs.
// ---------------------------------------------------------------------------

struct DtSelectorInfo {
    std::string name;
    SortId resultSort = NullSort;
};

struct DtConstructorInfo {
    std::string name;
    uint32_t index = 0;                  // position in the datatype's ctor list
    std::vector<DtSelectorInfo> selectors;
    uint32_t arity() const { return static_cast<uint32_t>(selectors.size()); }
};

struct DatatypeInfo {
    SortId sort = NullSort;
    std::vector<DtConstructorInfo> constructors;
    bool recursive = false;              // SOMTParser occurs-check result

    const DtConstructorInfo* constructorByName(const std::string& name) const {
        for (const auto& c : constructors) {
            if (c.name == name) return &c;
        }
        return nullptr;
    }
};

class DatatypeRegistry {
public:
    void addDatatype(DatatypeInfo info) {
        SortId s = info.sort;
        bySort_.emplace(s, std::move(info));
    }

    bool empty() const { return bySort_.empty(); }
    bool isDatatypeSort(SortId s) const { return bySort_.find(s) != bySort_.end(); }

    const DatatypeInfo* datatype(SortId s) const {
        auto it = bySort_.find(s);
        return it != bySort_.end() ? &it->second : nullptr;
    }

    // Resolve a constructor name within a datatype sort.
    const DtConstructorInfo* constructor(SortId sort, const std::string& name) const {
        const DatatypeInfo* dt = datatype(sort);
        return dt ? dt->constructorByName(name) : nullptr;
    }

    // Resolve a selector node: given the DATATYPE sort of the operand and the
    // selector name, return the (constructor, argIndex) it projects, or nullptr.
    // selectorOut receives the matching DtSelectorInfo.
    const DtConstructorInfo* selector(SortId datatypeSort, const std::string& name,
                                      uint32_t& argIndexOut) const {
        const DatatypeInfo* dt = datatype(datatypeSort);
        if (!dt) return nullptr;
        for (const auto& c : dt->constructors) {
            for (uint32_t i = 0; i < c.selectors.size(); ++i) {
                if (c.selectors[i].name == name) {
                    argIndexOut = i;
                    return &c;
                }
            }
        }
        return nullptr;
    }

    // Resolve a tester node: given the DATATYPE sort of the operand and the
    // tester payload name, return the constructor it tests. Accepts both the
    // bare constructor name ("cons") and the SMT-LIB "is-cons" form.
    const DtConstructorInfo* tester(SortId datatypeSort, const std::string& name) const {
        const DatatypeInfo* dt = datatype(datatypeSort);
        if (!dt) return nullptr;
        if (const auto* c = dt->constructorByName(name)) return c;
        if (name.rfind("is-", 0) == 0) {
            return dt->constructorByName(name.substr(3));
        }
        return nullptr;
    }

private:
    std::unordered_map<SortId, DatatypeInfo> bySort_;
};

} // namespace xolver
