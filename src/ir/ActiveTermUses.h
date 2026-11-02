#pragma once

#include "ir/NativeTerms.h"
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

// Reverse uses of the DAG reachable from a mutable set of root slots. Old IR
// nodes may remain allocated after rewriting; inactive parents are excluded.
class ActiveTermUses {
public:
    struct Closure {
        std::unordered_set<ExprId> terms;
        std::vector<size_t> roots;
    };

    explicit ActiveTermUses(const NativeTerms& ir) : ir_(ir) {}
    void setRoot(size_t slot, ExprId root);
    Closure variableClosure(const std::string& name);
    uint64_t work() const { return work_; }

private:
    void retain(ExprId root);
    void release(ExprId root);
    void grow(ExprId id);

    const NativeTerms& ir_;
    std::vector<ExprId> roots_;
    std::vector<size_t> references_;
    std::vector<bool> indexed_;
    std::vector<std::unordered_set<ExprId>> parents_;
    std::vector<std::unordered_set<size_t>> rootSlots_;
    std::unordered_map<std::string, std::vector<ExprId>> variables_;
    uint64_t work_ = 0;
};

} // namespace xolver
