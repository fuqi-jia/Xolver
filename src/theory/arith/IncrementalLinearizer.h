#pragma once

#include "expr/ir.h"
#include "theory/TheorySolver.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <vector>

namespace nlcolver {

/**
 * Incremental Linearizer: abstracts nonlinear terms into linear proxies.
 *
 * Stage F skeleton:
 *   - Sign lemmas: x > 0 ∧ y > 0 → x*y > 0
 *   - Interval lemmas: bounds propagation through nonlinear ops
 *   - McCormick relaxations: bilinear term envelopes
 */
class IncrementalLinearizer {
public:
    explicit IncrementalLinearizer(PolynomialKernel& kernel);

    struct Lemma {
        std::vector<SatLit> clause;
    };

    // Given a set of theory atoms, generate linearization lemmas.
    std::vector<Lemma> linearize(const std::vector<TheoryAtom>& atoms,
                                  const CoreIr& ir);

private:
    PolynomialKernel& kernel_;
};

} // namespace nlcolver
