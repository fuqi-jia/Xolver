#pragma once

#include "expr/ir.h"
#include "sat/SatSolver.h"
#include "frontend/atomization/ArithAtomExtractor.h"
#include "frontend/atomization/EufAtomExtractor.h"
#include "theory/core/DynamicAtomRegistrar.h"
#include <cassert>
#include <unordered_map>
#include <vector>

namespace xolver {

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
class Atomizer : public DynamicAtomRegistrar {
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
    SatLit registerDynamicAtom(ExprId expr, TheoryId theory) override;

    // Set the theory atom registry for registering parsed atoms.
    void setRegistry(TheoryAtomRegistry* registry) { registry_ = registry; arithExtractor_.setRegistry(registry); eufExtractor_.setRegistry(registry); }

    // Set the default theory ID for parsed linear atoms (LRA or LIA).
    void setDefaultTheory(TheoryId theory) { defaultTheory_ = theory; }

    // Set the arithmetic theory used in combination mode for non-UF expressions.
    void setCombinationArithTheory(TheoryId theory) { combinationArithTheory_ = theory; }

    // Set the polynomial kernel for NRA atom extraction.
    void setPolynomialKernel(PolynomialKernel* kernel) { arithExtractor_.setPolynomialKernel(kernel); }

    void setBoolSortId(SortId id) { boolSortId_ = id; }
    void setSharedTermRegistry(SharedTermRegistry* reg) { sharedTermRegistry_ = reg; }

    // XOLVER_PP_PG_CNF: Plaisted-Greenbaum polarity-aware CNF. When enabled, a
    // monotone connective (And/Or/Implies) emits only the half of its defining
    // biconditional that its OCCURRENCE polarity requires, roughly halving
    // clauses for single-polarity subformulas while staying equisatisfiable.
    void setPgCnf(bool on) { pgEnabled_ = on; }

    // PG pass 1: union the occurrence polarity of every subformula reachable
    // from `roots` (each asserted at positive polarity). Must be called before
    // atomize(); a no-op unless PG is enabled.
    void computePolarities(const std::vector<ExprId>& roots, const CoreIr& ir);

private:
    SatLit atomizeRec(ExprId eid, const CoreIr& ir);
    // Bottom-up iterative pre-pass over boolean-sorted subformulas: memoizes
    // every nested sub-formula before atomizeRec is invoked on its parent, so
    // the (recursive) atomizeRec never recurses deeper than one memo lookup.
    // Eliminates the deep-formula stack overflow without touching the encoding.
    void preAtomizeIterative(ExprId root, const CoreIr& ir);
    SatVar freshVar();

    // Which halves of a connective's defining biconditional to emit for `eid`:
    // {needPosDir (x->def), needNegDir (def->x)}. Full {true,true} unless PG is
    // enabled AND a polarity was recorded for `eid` (defensive: an unrecorded
    // node falls back to both halves, never dropping a clause).
    std::pair<bool, bool> pgDirs(ExprId eid) const;

    static bool isFormulaPositionTerm(Kind k);
    bool areAllChildrenBool(const CoreExpr& e, const CoreIr& ir) const;
    // True if `eid` is provably Boolean by sort registration OR by being a
    // Boolean-producing operator. Robust to sort-registration gaps (a declared
    // Bool variable can carry an unregistered SortId).
    bool isProvablyBool(ExprId eid, const CoreIr& ir) const;
    SatLit encodeBoolEq(ExprId eid, const CoreIr& ir);
    SatLit encodeBoolDistinct(ExprId eid, const CoreIr& ir);

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

    SatSolver& sat_;
    std::vector<AtomRecord> atoms_;
    std::unordered_map<ExprId, SatLit> memo_;
    SatVar nextVar_ = 1;
    TheoryAtomRegistry* registry_ = nullptr;
    TheoryId defaultTheory_ = TheoryId::LRA;
    TheoryId combinationArithTheory_ = TheoryId::LRA;
    SharedTermRegistry* sharedTermRegistry_ = nullptr;
    // iter-100: ExprId-keyed cache for containsArrayOrUf so DAG-shared
    // subtrees aren't re-walked on every Eq/Distinct routing decision.
    // Key: ExprId.id, value: true (has UF/array) / false (clean subtree).
    std::unordered_map<uint32_t, bool> containsArrayOrUfMemo_;

    SortId boolSortId_ = NullSort;
    SyntheticExprIdAllocator synthExprAlloc_;

    // PG-CNF (XOLVER_PP_PG_CNF). pol_ maps a subformula to its occurrence
    // polarity bitset: bit0 = occurs positively, bit1 = occurs negatively.
    bool pgEnabled_ = false;
    std::unordered_map<ExprId, uint8_t> pol_;

    ArithAtomExtractor arithExtractor_;
    EufAtomExtractor eufExtractor_;
};

} // namespace xolver
