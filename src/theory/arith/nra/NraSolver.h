#pragma once

#include "theory/TheorySolver.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include "theory/arith/nra/CdcacSolver.h"
#include <memory>

namespace nlcolver {

/**
 * NRA (Nonlinear Real Arithmetic) theory solver.
 *
 * Facade that delegates polynomial constraint checking to the
 * underlying CDCAC engine (CdcacSolver). Future phases may support
 * multiple NRA backends (e.g., local search, MCSAT) selected
 * dynamically.
 */
class NraSolver : public TheorySolver {
public:
    explicit NraSolver(std::unique_ptr<PolynomialKernel> kernel);

    TheoryId id() const override { return TheoryId::NRA; }

    // Expose kernel so Atomizer can share the same instance.
    PolynomialKernel* kernel() const { return kernel_.get(); }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit reason) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaDatabase& lemmaDb) override;
    void reset() override;

private:
    std::unique_ptr<PolynomialKernel> kernel_;
    std::unique_ptr<PolynomialConverter> converter_;
    CdcacSolver engine_;
};

} // namespace nlcolver
