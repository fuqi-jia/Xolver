#pragma once

#include <somtparser/passes/rewriter.h>

namespace zolver {

/**
 * Install Zolver-specific rewrite rules on top of SOMTParser defaults.
 *
 * Stage A rules:
 *   - Flip > / >= to < / <= (by negating RHS)
 *   - Flatten associative AND/OR/ADD/MUL
 *   - Normalize arithmetic comparisons to p - q ⋈ 0
 */
void installZolverRewriteRules(SOMTParser::Rewriter& r);

} // namespace zolver
