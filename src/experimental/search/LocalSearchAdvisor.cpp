#include "experimental/search/LocalSearchAdvisor.h"

namespace nlcolver {

void LocalSearchAdvisor::init(const CoreIr&) {}

LocalSearchAdvisor::ModelProposal LocalSearchAdvisor::propose() {
    return {};
}

void LocalSearchAdvisor::feedback(bool, double) {}
void LocalSearchAdvisor::restart() {}

} // namespace nlcolver
