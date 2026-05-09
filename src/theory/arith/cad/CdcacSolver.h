#pragma once

#include "theory/TheorySolver.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include <gmpxx.h>
#include <vector>
#include <memory>
#include <unordered_set>

namespace nlcolver {

/**
 * Minimal Conflict-Driven Cylindrical Algebraic Covering (CAlC) solver.
 *
 * Stage D MVP:
 *   - Handles univariate and simple bivariate polynomial constraints.
 *   - Uses libpoly for polynomial evaluation and root isolation.
 *   - Sample strategy: try rational values (0, 1, -1), then isolate roots.
 *   - Cell construction is rudimentary: interval cells for single variable.
 */
class CdcacSolver : public TheorySolver {
public:
    explicit CdcacSolver(std::unique_ptr<PolynomialKernel> kernel);

    TheoryId id() const override { return TheoryId::NRA; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtom& atom, bool value, const CoreIr& ir) override;
    TheoryCheckResult check(const CoreIr& ir) override;
    void reset() override;

private:
    struct PolyConstraint {
        SatVar satVar;
        PolyId poly;       // polynomial representing lhs - rhs
        Relation rel;      // original relation (after value flip)
    };

    std::unique_ptr<PolynomialKernel> kernel_;
    std::unique_ptr<PolynomialConverter> converter_;
    std::vector<PolyConstraint> constraints_;
    std::unordered_set<std::string> allVars_;
    std::optional<TheoryConflict> lastConflict_;

    void collectVars(ExprId eid, const CoreIr& ir);

    bool evaluateAtSample(const std::vector<PolyConstraint>& constraints,
                          const std::unordered_map<std::string, mpq_class>& sample);
    TheoryCheckResult trySolve(const CoreIr& ir);
};

} // namespace nlcolver
