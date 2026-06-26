#pragma once
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "theory/arith/logics/nra/core/CdcacTypes.h"
#include "theory/arith/logics/nra/core/CdcacConstraint.h"
#include <string>
#include <vector>

namespace xolver {

// Degree-stratified CDCAC variable order. Primary key: ascending total-degree
// sum (highest-degree var LAST). Tie-break within a stratum: descending
// frontScore (linearizing/connected/tableau-bounded vars placed later). Final
// tie-break: original position. Returns a permutation of exactly `varNames`.
std::vector<std::string> computeCdcacVarOrder(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& constraints,
    const std::vector<std::string>& varNames);

} // namespace xolver
