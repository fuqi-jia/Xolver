#include "search/experimental/search/LocalSearchAdvisor.h"

namespace xolver {

void LocalSearchAdvisor::init(const NativeTerms&) {}

LocalSearchAdvisor::ModelProposal LocalSearchAdvisor::propose() {
    return {};
}

void LocalSearchAdvisor::feedback(bool, double) {}
void LocalSearchAdvisor::restart() {}

} // namespace xolver
