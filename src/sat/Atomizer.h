#pragma once

#include "expr/ir.h"
#include "sat/SatSolver.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include "theory/euf/EufTypes.h"
#include <cassert>
#include <unordered_map>
#include <vector>

namespace nlcolver {

class TheoryAtomRegistry;
class SharedTermRegistry;

/**
 * Atomizer: extracts boolean atoms from CoreExpr and builds SAT clauses.
 *
 * Stage A minimal version:
 * - Boolean variables -> SAT literals.
 * - And/Or/Not/Implies -> CNF via Tseitin or direct unit clauses.
 * - Theory atoms (arithmetic comparisons) -> SAT literal + TheoryAtom record.
 */
class Atomizer {
public:
    struct AtomRecord {
        SatVar var;
        ExprId expr;
        bool isTheory;
        TheoryId theory;
    };

    explicit Atomizer(SatSolver& sat);

    // Convert a single assertion expression into SAT clauses.
    // Returns the SAT literal that is equivalent to the expression.
    SatLit atomize(ExprId root, const CoreIr& ir);

    const std::vector<AtomRecord>& atoms() const { return atoms_; }

    // Register a dynamically created theory atom (e.g. branch split, disequality split).
    // Returns the SAT literal. The exprId should be a synthetic id (not in CoreIr).
    SatLit registerDynamicAtom(ExprId expr, TheoryId theory);

    // Set the theory atom registry for registering parsed atoms.
    void setRegistry(TheoryAtomRegistry* registry) { registry_ = registry; }

    // Set the default theory ID for parsed linear atoms (LRA or LIA).
    void setDefaultTheory(TheoryId theory) { defaultTheory_ = theory; }

    // Set the arithmetic theory used in combination mode for non-UF expressions.
    void setCombinationArithTheory(TheoryId theory) { combinationArithTheory_ = theory; }

    // Set the polynomial kernel for NRA atom extraction.
    void setPolynomialKernel(PolynomialKernel* kernel) {
        polyKernel_ = kernel;
        polyConverter_ = std::make_unique<PolynomialConverter>(*kernel);
    }

    void setBoolSortId(SortId id) { boolSortId_ = id; }
    void setSharedTermRegistry(SharedTermRegistry* reg) { sharedTermRegistry_ = reg; }

private:
    SatLit atomizeRec(ExprId eid, const CoreIr& ir);
    SatVar freshVar();

    bool extractPolynomialConstraint(ExprId eid, const CoreIr& ir, SatVar v, TheoryId theory);

    // EUF atom dedup: canonical key -> existing SAT literal
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

    class SyntheticExprIdAllocator {
        static constexpr ExprId SyntheticStart = std::numeric_limits<ExprId>::max() - 100;
        ExprId nextId_ = SyntheticStart;
    public:
        ExprId next() {
            assert(nextId_ != TrueSentinelExpr);
            assert(nextId_ != FalseSentinelExpr);
            assert(nextId_ > 0);
            return nextId_--;
        }
        void reset() { nextId_ = SyntheticStart; }
    };

    SatLit getOrCreateEufAtom(EufAtomPayload payload, ExprId originExpr);
    SatLit atomizeNaryEufEq(ExprId eid, const CoreIr& ir);
    SatLit atomizeNaryEufDistinct(ExprId eid, const CoreIr& ir);
    static bool isFormulaPositionTerm(Kind k);

    bool areAllChildrenBool(const CoreExpr& e, const CoreIr& ir) const;
    SatLit encodeBoolEq(ExprId eid, const CoreIr& ir);
    SatLit encodeBoolDistinct(ExprId eid, const CoreIr& ir);

    SatSolver& sat_;
    std::vector<AtomRecord> atoms_;
    std::unordered_map<ExprId, SatLit> memo_;
    SatVar nextVar_ = 1;
    TheoryAtomRegistry* registry_ = nullptr;
    TheoryId defaultTheory_ = TheoryId::LRA;
    TheoryId combinationArithTheory_ = TheoryId::LRA;
    PolynomialKernel* polyKernel_ = nullptr;
    std::unique_ptr<PolynomialConverter> polyConverter_;
    SharedTermRegistry* sharedTermRegistry_ = nullptr;

    SortId boolSortId_ = NullSort;
    SyntheticExprIdAllocator synthExprAlloc_;
    std::unordered_map<EufAtomKey, SatLit, EufAtomKeyHash> eufAtomDedup_;
};

} // namespace nlcolver
