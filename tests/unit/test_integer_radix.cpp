#include "search/bitblast/IntegerRadixEncoder.h"
#include <doctest/doctest.h>

using namespace xolver;
using namespace xolver::bitblast;

TEST_CASE("Integer radix encoding: exhaustive signed inputs preserve exact values and prevent wrapping") {
    for (bool negate : {false, true}) for (int offset : {-19, 0, 21}) {
        auto sat = createSatSolver();
        BitBlastEncoder encoder(*sat);
        std::unordered_map<std::string, BitVec> values{
            {"word", encoder.mkVar(8)}, {"q", encoder.mkVar(4)}, {"r", encoder.mkVar(5)}};
        const auto q = values.at("q"), r = values.at("r");
        const IntegerBoundsLookup bounds = [&](const std::string& name)
            -> std::optional<std::pair<mpz_class, mpz_class>> {
            if (name == "word") return std::pair<mpz_class, mpz_class>{-16-offset, 15-offset};
            return std::nullopt;
        };
        WorkBudget budget;
        const auto applied = encodeIntegerRadixDefinitions(encoder,
            {{"word", "q", "r", mpz_class(offset), 3, negate, 0, 7}}, values,
            bounds, budget, std::chrono::steady_clock::time_point::max());
        REQUIRE(applied == std::vector<size_t>{0});
        REQUIRE_FALSE(encoder.overflowed());
        // Remainders wider than their proved domain must be constrained,
        // rather than silently truncated. Signed quotient overflow must also
        // be rejected instead of wrapping into a spurious target value.
        for (int high = -4; high <= 3; ++high) for (int low = -16; low <= 15; ++low) {
            std::vector<SatLit> assumptions;
            auto fix = [&](const BitVec& bits, int value) {
                const mpz_class integer(value);
                for (unsigned bit = 0; bit < bits.width(); ++bit)
                    assumptions.push_back(mpz_tstbit(integer.get_mpz_t(), bit)
                        ? bits.bits[bit] : bits.bits[bit].negated());
            };
            fix(q, high); fix(r, low);
            const int expected = (negate ? -8 : 8)*high + low - offset;
            const bool validRemainder = low >= 0 && low < 8;
            // At offset zero the target domain is exactly its signed width;
            // for other offsets check all inputs inside the asserted domain.
            const bool inRange = expected >= -16-offset && expected <= 15-offset;
            if (offset != 0 && validRemainder && !inRange) continue;
            const auto status = sat->solve(assumptions);
            CHECK(status == (validRemainder && inRange
                ? SatSolver::SolveResult::Sat : SatSolver::SolveResult::Unsat));
            if (status == SatSolver::SolveResult::Sat)
                CHECK(readBitVec(*sat, values.at("word")) == expected);
        }
    }
}

TEST_CASE("Integer radix encoding: resource exhaustion cannot expose a completed definition") {
    auto sat = createSatSolver();
    BitBlastEncoder encoder(*sat);
    std::unordered_map<std::string, BitVec> values{
        {"word", encoder.mkVar(8)}, {"q", encoder.mkVar(4)}, {"r", encoder.mkVar(5)}};
    const auto original = values.at("word").bits;
    const IntegerBoundsLookup bounds = [](const std::string&)
        -> std::optional<std::pair<mpz_class, mpz_class>> { return std::nullopt; };
    WorkBudget budget(2);
    CHECK_THROWS_AS(encodeIntegerRadixDefinitions(encoder,
        {{"word", "q", "r", 0, 3, false, 0, 7}}, values, bounds, budget,
        std::chrono::steady_clock::time_point::max()), ResourceExhausted);
    CHECK(values.at("word").bits == original);
}
