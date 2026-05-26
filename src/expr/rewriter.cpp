#include "expr/rewriter.h"

namespace zolver {

using namespace SOMTParser;

/**
 * Stage A: minimal Zolver-specific rewrite rules.
 *
 * For now, we rely on SOMTParser's default rules (NOT, AND, ADD simplification).
 * Future rules:
 *   - Flatten associative AND/OR/ADD/MUL
 *   - Normalize comparisons: p > q → p - q > 0, then flip > to <
 *   - Arithmetic constant folding
 */
void installZolverRewriteRules(Rewriter& /*r*/) {
    // TODO: register custom rules via r.rules().onGT(...), onGE(...), etc.
    // For Stage A, the default rules plus adapter-side GT/GE flipping suffice.
}

} // namespace zolver
