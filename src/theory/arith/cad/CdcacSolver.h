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
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb) override;
    void reset() override;

private:
    struct PolyConstraint {
        SatVar satVar;
        PolyId poly;
        Relation rel;
    };

    struct TrailEntry {
        int level;
        size_t constraintsSize;
    };

    std::unique_ptr<PolynomialKernel> kernel_;
    std::unique_ptr<PolynomialConverter> converter_;
    std::vector<PolyConstraint> constraints_;
    std::vector<TrailEntry> trail_;
    std::unordered_set<std::string> allVars_;

    void collectVars(const std::vector<std::pair<std::string, mpq_class>>& coeffs);
};

} // namespace nlcolver
