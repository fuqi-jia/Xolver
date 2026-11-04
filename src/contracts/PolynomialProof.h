#pragma once

#include "ir/types.h"
#include <gmpxx.h>
#include <map>
#include <vector>

namespace xolver {

// Certificate interchange data. Powers are positive and sorted by variable;
// the empty monomial is the constant. This carries no solver ring operations.
using ProofMonomial = std::vector<std::pair<VarId, int>>;
using PolynomialProof = std::map<ProofMonomial, mpq_class>;

} // namespace xolver
