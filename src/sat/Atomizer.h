#pragma once

#include "expr/ir.h"
#include "sat/SatSolver.h"
#include <unordered_map>
#include <vector>

namespace nlcolver {

class TheoryAtomRegistry;

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

private:
    SatLit atomizeRec(ExprId eid, const CoreIr& ir);
    SatVar freshVar();

    SatSolver& sat_;
    std::vector<AtomRecord> atoms_;
    std::unordered_map<ExprId, SatLit> memo_;
    SatVar nextVar_ = 1;
    TheoryAtomRegistry* registry_ = nullptr;
    TheoryId defaultTheory_ = TheoryId::LRA;
};

} // namespace nlcolver
