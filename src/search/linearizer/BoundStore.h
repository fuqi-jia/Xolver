#pragma once

#include "search/linearizer/LinearizationTypes.h"
#include <optional>
#include <string>

namespace xolver {

/**
 * BoundStore: read-only interface for looking up variable bounds.
 *
 * Adapters wrap DomainStore (NIA) or ReasonedBox (NRA/interval).
 */
class BoundStore {
public:
    virtual ~BoundStore() = default;
    virtual std::optional<LinearizationBounds> get(const std::string& var) const = 0;
};

} // namespace xolver
