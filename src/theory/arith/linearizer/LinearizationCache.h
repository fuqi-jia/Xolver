#pragma once

#include "theory/arith/linearizer/LinearizationTypes.h"
#include <unordered_set>

namespace zolver {

class LinearizationCache {
public:
    bool hasEmitted(const NonlinearTermKey& key,
                    SatLit nonlinearReason,
                    const std::vector<mpq_class>& boundValues,
                    int cutIndex);

    void markEmitted(const NonlinearTermKey& key,
                     SatLit nonlinearReason,
                     const std::vector<mpq_class>& boundValues,
                     int cutIndex);

    void clear();

private:
    std::unordered_set<CutCacheKey, CutCacheKeyHash> emitted_;
};

} // namespace zolver
