#pragma once

#include "theory/arith/linearizer/BoundStore.h"
#include "theory/arith/nia/core/DomainStore.h"

namespace nlcolver {

/**
 * DomainStoreBoundStore: adapts NIA DomainStore to BoundStore interface.
 */
class DomainStoreBoundStore : public BoundStore {
public:
    explicit DomainStoreBoundStore(const DomainStore& ds);
    std::optional<BoundInfo> get(const std::string& var) const override;

private:
    const DomainStore& ds_;
};

} // namespace nlcolver
