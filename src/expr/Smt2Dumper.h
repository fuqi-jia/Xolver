#pragma once

#include "expr/ir.h"
#include <string>
#include <vector>

namespace xolver {

std::string dumpExprToSMT2(ExprId id, const CoreIr& ir);

// Dump the IR as a self-contained SMT-LIB problem: (set-logic ALL), a
// (declare-const ...) for every free variable in `assertions`, one (assert ...)
// per assertion, then (check-sat). A theory proof's `assume` terms reference
// these same (post-normalization) IR atoms, so the proof is checked against THIS
// problem; the original->IR normalization is a trusted preprocessing step (the
// same boundary as Phase B's DRAT-vs-captured-CNF).
std::string dumpProblemToSMT2(const CoreIr& ir, const std::vector<ExprId>& assertions);

} // namespace xolver
