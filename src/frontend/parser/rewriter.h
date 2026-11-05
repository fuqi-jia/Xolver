#pragma once

#include <somtparser/parser.h>

namespace xolver {

/**
 * Install Xolver-specific rewrite rules on top of SOMTParser defaults.
 *
 * Stage A rules:
 *   - Flip > / >= to < / <= (by negating RHS)
 *   - Flatten associative AND/OR/ADD/MUL
 *   - Normalize arithmetic comparisons to p - q ⋈ 0
 */
void installXolverRewriteRules(SOMTParser::Rewriter& r);

} // namespace xolver
