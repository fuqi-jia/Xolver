#pragma once
#include <somtparser/core/options.h>
namespace xolver {
// Preserve theory semantics for exact native backends. Parsing must not decide
// FP equality or evaluate Unicode operations using host floating-point/bytes.
inline void preserveNativeTheories(SOMTParser::GlobalOptions &options) {
    using K = SOMTParser::NODE_KIND;
    for (int k = int(K::NT_FP_ADD); k <= int(K::NT_FP_IS_POS); ++k)
        options.preserveOperator(K(k));
    for (int k = int(K::NT_STR_LEN); k <= int(K::NT_REG_LOOP); ++k)
        options.preserveOperator(K(k));
    options.preserveOperators({K::NT_EQ, K::NT_EQ_BOOL, K::NT_EQ_OTHER, K::NT_DISTINCT,
                               K::NT_DISTINCT_BOOL, K::NT_DISTINCT_OTHER});
}
} // namespace xolver
