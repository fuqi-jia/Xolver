#pragma once

#include <somtparser/passes/rewriter.h>

namespace nlcolver {

/**
 * Install NLColver-specific rewrite rules on top of SOMTParser defaults.
 *
 * Stage A rules:
 *   - Flip > / >= to < / <= (by negating RHS)
 *   - Flatten associative AND/OR/ADD/MUL
 *   - Normalize arithmetic comparisons to p - q ⋈ 0
 */
void installNlcolverRewriteRules(SOMTParser::Rewriter& r);

} // namespace nlcolver
