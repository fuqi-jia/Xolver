#pragma once

#include "expr/ir.h"
#include "sat/SatSolver.h"
#include "theory/euf/EufTypes.h"
#include <unordered_map>
#include <functional>

namespace nlcolver {

class TheoryAtomRegistry;
class CoreIr;

/**
 * EufAtomExtractor: extracts EUF theory atoms from CoreExpr.
 *
 * This helper is used by Atomizer to handle EUF-specific atom extraction.
 * It does not own SAT state; all SAT operations are done via callbacks.
 */
class EufAtomExtractor {
public:
    void setRegistry(TheoryAtomRegistry* registry) { registry_ = registry; }

    // Get or create an EUF atom. Returns the SAT literal.
    // freshVar: callback to allocate a new SAT variable.
    // recordAtom: callback to record the atom in the parent Atomizer.
    SatLit getOrCreateAtom(
        const EufAtomPayload& payload,
        ExprId originExpr,
        std::unordered_map<ExprId, SatLit>& memo,
        const std::function<SatVar()>& freshVar,
        const std::function<void(SatVar, ExprId, bool, TheoryId)>& recordAtom);

    // Create n-ary equality atom (pairwise decomposition).
    // addClause: callback to add a clause to the SAT solver.
    // atomizeRec: callback to recursively atomize child expressions.
    SatLit atomizeNaryEq(
        ExprId eid, const CoreIr& ir,
        std::unordered_map<ExprId, SatLit>& memo,
        const std::function<SatVar()>& freshVar,
        const std::function<void(const std::vector<SatLit>&)>& addClause,
        const std::function<SatLit(ExprId)>& atomizeRec);

    // Create n-ary distinct atom (pairwise decomposition).
    SatLit atomizeNaryDistinct(
        ExprId eid, const CoreIr& ir,
        std::unordered_map<ExprId, SatLit>& memo,
        const std::function<SatVar()>& freshVar,
        const std::function<void(const std::vector<SatLit>&)>& addClause,
        const std::function<SatLit(ExprId)>& atomizeRec);

private:
    struct EufAtomKey {
        ExprId lhs;
        ExprId rhs;
        Relation rel;
        EufAtomKind kind;
        bool operator==(const EufAtomKey& o) const {
            return lhs == o.lhs && rhs == o.rhs && rel == o.rel && kind == o.kind;
        }
    };
    struct EufAtomKeyHash {
        std::size_t operator()(const EufAtomKey& k) const {
            std::size_t h = std::hash<ExprId>{}(k.lhs);
            h ^= std::hash<ExprId>{}(k.rhs) + 0x9e3779b9 + (h << 6) + (h >> 2);
            h ^= static_cast<std::size_t>(k.rel) + 0x9e3779b9 + (h << 6) + (h >> 2);
            h ^= static_cast<std::size_t>(k.kind) + 0x9e3779b9 + (h << 6) + (h >> 2);
            return h;
        }
    };

    TheoryAtomRegistry* registry_ = nullptr;
    std::unordered_map<EufAtomKey, SatLit, EufAtomKeyHash> dedup_;
};

} // namespace nlcolver
