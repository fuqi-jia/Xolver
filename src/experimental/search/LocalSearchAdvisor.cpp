#include "experimental/search/LocalSearchAdvisor.h"

namespace zolver {

void LocalSearchAdvisor::init(const CoreIr&) {}

LocalSearchAdvisor::ModelProposal LocalSearchAdvisor::propose() {
    return {};
}

void LocalSearchAdvisor::feedback(bool, double) {}
void LocalSearchAdvisor::restart() {}

} // namespace zolver
