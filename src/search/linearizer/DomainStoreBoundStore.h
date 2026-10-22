#pragma once

#include "search/linearizer/BoundStore.h"
#include "search/nia/core/DomainStore.h"

namespace xolver {

/**
 * DomainStoreBoundStore: adapts NIA DomainStore to BoundStore interface.
 */
class DomainStoreBoundStore : public BoundStore {
public:
    explicit DomainStoreBoundStore(const DomainStore& ds);
    std::optional<LinearizationBounds> get(const std::string& var) const override;

private:
    const DomainStore& ds_;
};

} // namespace xolver
