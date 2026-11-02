#pragma once

#include "base/WorkBudget.h"
#include "search/bitblast/BitBlastEncoder.h"
#include <chrono>
#include <optional>
#include <utility>

namespace xolver::bitblast {

struct EncodedIntegerDomain {
    BitVec value;
    // Exactly one selector is true, and value equals its arbitrary-size point.
    std::vector<std::pair<mpz_class, SatLit>> choices;
};

// Encode a finite set of integer points without representing the intervening
// interval. Selectors and signed bits share one exact value representation.
// Empty domains or exhausted resources expose no completed encoding.
std::optional<EncodedIntegerDomain> encodeIntegerFiniteDomain(
    BitBlastEncoder& encoder, std::vector<mpz_class> points, WorkBudget& budget,
    std::chrono::steady_clock::time_point deadline =
        std::chrono::steady_clock::time_point::max());

} // namespace xolver::bitblast
