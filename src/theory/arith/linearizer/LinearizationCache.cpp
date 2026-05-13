#include "theory/arith/linearizer/LinearizationCache.h"

namespace nlcolver {

bool LinearizationCache::hasEmitted(const NonlinearTermKey& key,
                                     SatLit nonlinearReason,
                                     const std::vector<mpq_class>& boundValues,
                                     int cutIndex) {
    CutCacheKey cacheKey{key, nonlinearReason, boundValues, cutIndex};
    return emitted_.count(cacheKey) > 0;
}

void LinearizationCache::markEmitted(const NonlinearTermKey& key,
                                      SatLit nonlinearReason,
                                      const std::vector<mpq_class>& boundValues,
                                      int cutIndex) {
    CutCacheKey cacheKey{key, nonlinearReason, boundValues, cutIndex};
    emitted_.insert(std::move(cacheKey));
}

void LinearizationCache::clear() {
    emitted_.clear();
}

} // namespace nlcolver
