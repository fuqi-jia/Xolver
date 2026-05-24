#pragma once

// Capability 4 — Domain-aware Univariate Polynomial Sign / Interval Analyzer.
//
// For each active atom p(x) rel 0 with exactly one variable, isolates the real
// roots of p (via libpoly, any degree), builds the sign-invariant decomposition
// of ℝ, and forms the satisfying IntervalSet.  Then:
//   - Real: empty satisfying set ⇒ DerivedConflict; universe ⇒ satisfied; else
//     a DerivedBound (intersected with the active bound).
//   - Int : no integer in the satisfying set ⇒ DerivedConflict; else a
//     DerivedBound, integer-interpreted by IntervalSet's integer helpers.

#include "theory/arith/presolve/Presolve.h"
#include <memory>

namespace nlcolver {

class LibpolyBackend;

class UnivariatePolySignAnalyzer : public PresolveCapability {
public:
    UnivariatePolySignAnalyzer();
    ~UnivariatePolySignAnalyzer() override;  // out-of-line (LibpolyBackend is incomplete here)
    const char* name() const override { return "UnivariatePolySignAnalyzer"; }
    bool run(PresolveState& st) override;

private:
    std::unique_ptr<LibpolyBackend> backend_;  // lazily constructed from st.kernel
};

} // namespace nlcolver
