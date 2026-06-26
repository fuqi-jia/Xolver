#pragma once

// Capability 7 — Bound-Chain Composer.
//
// Given two active atoms that bound a common variable v from opposite sides
// (p(x) ⋈₁ v and v ⋈₂ q(x), both with ⋈ ∈ {<, ≤}), composes them into the
// transitive consequence p(x) ⋈ q(x) (strict if either input is strict).  In
// poly-form terms, the two atoms have v with opposite-sign linear coefficients;
// scaling each to unit |coeff| and adding cancels v.  The composed atom is
// added (when univariate, for Cap. 4 to analyze) with the two inputs as reason.

#include "theory/arith/kernel/presolve/Presolve.h"

namespace xolver {

class BoundChainComposer : public PresolveCapability {
public:
    const char* name() const override { return "BoundChainComposer"; }
    bool run(PresolveState& st) override;
};

} // namespace xolver
