#include "search/linear/IntegerModelCompletion.h"
#include "search/lra/GeneralSimplex.h"

#include <algorithm>
#include <array>

namespace xolver {

std::optional<SimplexIntegerPoint> completeIntegerModel(
    GeneralSimplex& simplex, std::span<const int> columns,
    std::chrono::steady_clock::time_point deadline, size_t nodeLimit,
    const std::function<void()>& tick, IntegerCompletionStatistics* statistics) {
    IntegerCompletionStatistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    const auto decision = SatLit::positive(0); // local; no explanation escapes
    auto search = [&](auto&& self) -> std::optional<SimplexIntegerPoint> {
        tick();
        if (stats.nodes >= nodeLimit || std::chrono::steady_clock::now() >= deadline) {
            stats.exhausted = true;
            return std::nullopt;
        }
        ++stats.nodes;
        const auto feasible = simplex.checkUntil(deadline);
        if (feasible != GeneralSimplex::Result::Sat) {
            stats.exhausted |= feasible == GeneralSimplex::Result::Unknown;
            return std::nullopt;
        }
        const auto delta = simplex.computeSafeDelta();
        SimplexIntegerPoint point;
        int fractional = -1;
        mpq_class bestDistance = 0, value;
        for (const int column : columns) {
            tick();
            const auto current = simplex.value(column);
            const mpq_class q = current.a + current.b * delta;
            point.emplace(column, q);
            if (q.get_den() == 1) continue;
            mpz_class floor;
            mpz_fdiv_q(floor.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
            const mpq_class fraction = q - floor;
            const mpq_class distance = std::min(fraction, mpq_class(1 - fraction));
            if (fractional < 0 || distance > bestDistance) {
                fractional = column;
                bestDistance = distance;
                value = q;
            }
        }
        if (fractional < 0) return point;
        ++stats.fractionalPoints;
        mpz_class floor;
        mpz_fdiv_q(floor.get_mpz_t(), value.get_num().get_mpz_t(), value.get_den().get_mpz_t());
        std::array<mpq_class, 2> neighbors{mpq_class(floor), mpq_class(floor + 1)};
        if (value - neighbors[0] > neighbors[1] - value) std::swap(neighbors[0], neighbors[1]);
        for (const auto& neighbor : neighbors) {
            tick();
            if (stats.exhausted) break;
            simplex.push();
            std::optional<SimplexIntegerPoint> result;
            try {
                ++stats.pins;
                const BoundInfo pin(BoundValue(DeltaRational(neighbor)), decision);
                if (simplex.assertLower(fractional, pin) && simplex.assertUpper(fractional, pin))
                    result = self(self);
            } catch (...) {
                simplex.pop(GeneralSimplex::AssignmentPolicy::Preserve);
                throw;
            }
            simplex.pop(GeneralSimplex::AssignmentPolicy::Preserve);
            if (result) return result;
        }
        return std::nullopt;
    };
    return search(search);
}

} // namespace xolver
