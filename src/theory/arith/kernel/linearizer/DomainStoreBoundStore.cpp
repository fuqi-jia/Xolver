#include "theory/arith/kernel/linearizer/DomainStoreBoundStore.h"

namespace xolver {

DomainStoreBoundStore::DomainStoreBoundStore(const DomainStore& ds)
    : ds_(ds) {}

std::optional<BoundInfo> DomainStoreBoundStore::get(const std::string& var) const {
    const IntDomain* d = ds_.getDomain(var);
    if (!d) return std::nullopt;

    BoundInfo info;
    if (d->hasLower) {
        info.hasLower = true;
        info.lower = mpq_class(d->lower.value);
        info.lowerReasons = d->lower.reasons;
        info.lowerReasonComplete = !d->lower.reasons.empty();
    }
    if (d->hasUpper) {
        info.hasUpper = true;
        info.upper = mpq_class(d->upper.value);
        info.upperReasons = d->upper.reasons;
        info.upperReasonComplete = !d->upper.reasons.empty();
    }
    return info;
}

} // namespace xolver
