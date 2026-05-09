#include "theory/arith/IncrementalLinearizer.h"

namespace nlcolver {

IncrementalLinearizer::IncrementalLinearizer(PolynomialKernel& kernel) : kernel_(kernel) {}

std::vector<IncrementalLinearizer::Lemma>
IncrementalLinearizer::linearize(const std::vector<TheoryAtom>&,
                                  const CoreIr&) {
    // Stage F: TODO implement sign/interval/McCormick lemmas.
    return {};
}

} // namespace nlcolver
