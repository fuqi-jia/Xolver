#include "search/lra/LraPropagationEngine.h"
#include <algorithm>
#include <array>
#include <chrono>
#include <deque>
#include <map>
#include <optional>

namespace xolver {
namespace {

struct LiteralLess {
    bool operator()(SatLit a, SatLit b) const {
        return a.var != b.var ? a.var < b.var : a.sign < b.sign;
    }
};

struct ExplainedEndpoint {
    std::optional<DeltaRational> value;
    std::vector<SatLit> reasons;
    // An unconditional derived bound has an empty, valid explanation.
    bool explained = false;
    bool usable() const { return value.has_value() && explained; }
};

struct Contribution {
    DeltaRational value;
    std::vector<SatLit> reasons;
    bool available = false;

    Contribution(const ExplainedEndpoint& endpoint, const mpq_class& coefficient) {
        if (coefficient == 0) { available = true; return; }
        if (!endpoint.usable()) return;
        value = coefficient * *endpoint.value;
        reasons = endpoint.reasons;
        available = true;
    }
};

struct RowAggregate {
    DeltaRational sum;
    size_t missing = 0;
    std::map<SatLit, size_t, LiteralLess> reasonCounts;

    void add(const Contribution& contribution) {
        if (!contribution.available) { ++missing; return; }
        sum += contribution.value;
        for (const auto reason : contribution.reasons) ++reasonCounts[reason];
    }

    std::optional<std::vector<SatLit>> explain(
        const Contribution* excluded, const std::vector<SatLit>& required,
        int maxReasons) const {
        std::vector<SatLit> result = required; // sorted and unique
        if (static_cast<int>(result.size()) > maxReasons) return std::nullopt;
        for (const auto& [reason, count] : reasonCounts) {
            const bool removed = excluded && excluded->available &&
                std::binary_search(excluded->reasons.begin(), excluded->reasons.end(),
                                   reason, LiteralLess{});
            if (count == static_cast<size_t>(removed)) continue;
            if (!std::binary_search(required.begin(), required.end(), reason, LiteralLess{}))
                result.push_back(reason);
            if (static_cast<int>(result.size()) > maxReasons) return std::nullopt;
        }
        std::sort(result.begin(), result.end(), LiteralLess{});
        return result;
    }
};

} // namespace

std::vector<LraPropagationEngine::ExplainedBound>
LraPropagationEngine::propagateAll(const GeneralSimplex& gs,
                                  const PropagationBudget& budget,
                                  Statistics* statistics,
                                  const BoundConsumer& consume) {
    if (statistics) *statistics = {};
    std::vector<ExplainedBound> accepted;
    if (budget.maxDerivedBounds <= 0 || budget.maxIterations <= 0 ||
        budget.maxReasonSize < 0 || budget.maxTimeMs <= 0) return accepted;
    const auto started = std::chrono::steady_clock::now();
    auto consumerTime = std::chrono::steady_clock::duration::zero();
    bool consumerStopped = false;
    auto exhausted = [&] {
        return consumerStopped || static_cast<int>(accepted.size()) >= budget.maxDerivedBounds ||
            std::chrono::steady_clock::now() - started - consumerTime >=
                std::chrono::milliseconds(budget.maxTimeMs);
    };

    // Values and explanations are local to this call. No stale state can
    // survive a simplex mutation, backtrack or a subsequent propagation run.
    std::vector<std::array<ExplainedEndpoint, 2>> bounds(gs.numVars());
    for (int var = 0; var < gs.numVars(); ++var) {
        const auto state = gs.varState(var);
        const BoundInfo* sources[] = {&state.lower, &state.upper};
        for (size_t side = 0; side < 2; ++side) {
            if (!sources[side]->bound.isFinite()) continue;
            auto& target = bounds[var][side];
            target.value = sources[side]->bound.value;
            if (sources[side]->reason) {
                target.reasons.push_back(*sources[side]->reason);
                target.explained = true;
            }
        }
    }

    struct WorkItem { int basic; bool lower; };
    std::deque<WorkItem> work;
    std::vector<std::array<bool, 2>> queued(gs.numVars(), {false, false});
    auto enqueue = [&](int basic, bool lower) {
        const size_t side = lower ? 0 : 1;
        if (queued[basic][side]) return;
        queued[basic][side] = true;
        work.push_back({basic, lower});
    };
    const auto seedCount = 2 * static_cast<std::size_t>(gs.tableau().numRows());
    if (seedCount != 0) {
        auto seed = nextSeed_ % seedCount;
        for (std::size_t count = 0; count < seedCount; ++count) {
            const int basic = gs.tableau().row(static_cast<int>(seed / 2)).basicVar;
            if (basic >= 0) enqueue(basic, seed % 2 == 0);
            if (++seed == seedCount) seed = 0;
        }
    }

    // The tableau is immutable during this call. Only updates to non-basic
    // endpoints can change a row's input contributions; derived basic bounds
    // are read separately when propagating backward. Keep just the most recent
    // row, so adjacent lower/upper visits can share arithmetic and explanations.
    // Every object here dies before a backtrack or the next theory check.
    struct RowSnapshot {
        int basic = -1;
        std::size_t revision = 0;
        bool insufficientBounds = false;
        std::vector<std::array<Contribution, 2>> contributions;
        RowAggregate minimum, maximum;
    };
    std::optional<RowSnapshot> snapshot;
    std::size_t inputRevision = 0;

    auto publish = [&](int var, bool lower, const DeltaRational& value,
                       const RowAggregate& aggregate, const Contribution* excluded,
                       const std::vector<SatLit>& required) {
        if (exhausted()) return false;
        auto& target = bounds[var][lower ? 0 : 1];
        if (target.value && (lower ? value <= *target.value : value >= *target.value))
            return false;
        // Materialize explanations only for a genuinely stronger bound.
        auto reasons = aggregate.explain(excluded, required, budget.maxReasonSize);
        if (!reasons) return false;
        if (gs.basicRowOfVar(var) < 0) ++inputRevision;
        target.value = value;
        target.reasons = *reasons;
        target.explained = true;
        accepted.push_back({var, lower, value, std::move(*reasons)});
        if (consume) {
            const auto beforeConsumer = std::chrono::steady_clock::now();
            consumerStopped = !consume(accepted.back());
            consumerTime += std::chrono::steady_clock::now() - beforeConsumer;
        }
        return true;
    };

    int iterations = 0;
    while (!work.empty() && iterations < budget.maxIterations && !exhausted()) {
        const auto item = work.front();
        work.pop_front();
        queued[item.basic][item.lower ? 0 : 1] = false;
        ++iterations;
        const int rowIndex = gs.basicRowOfVar(item.basic);
        if (rowIndex < 0) continue;
        // Advance before processing: all budget exits, including a bound-count
        // limit reached mid-row, give the next direction an opportunity on the
        // following check. The current call still uses its own local overlay.
        nextSeed_ = 2 * static_cast<std::size_t>(rowIndex) + (item.lower ? 1 : 2);
        if (nextSeed_ == seedCount) nextSeed_ = 0;
        const auto& row = gs.tableau().row(rowIndex);

        if (statistics) ++statistics->rowVisits;
        if (!snapshot || snapshot->basic != item.basic || snapshot->revision != inputRevision) {
            snapshot.emplace();
            snapshot->basic = item.basic;
            snapshot->revision = inputRevision;
            auto& contributions = snapshot->contributions;
            if (statistics) ++statistics->rowSnapshots;
            // A forward bound needs every contribution. A backward bound also
            // needs an explained basic endpoint and may omit only its target.
            // Stop when the inspected prefix rules out every deduction, before
            // rational arithmetic and explanation construction. A skipped row
            // cannot create a basic endpoint itself; a non-basic update changes
            // inputRevision and requeues the row before it can become useful.
            const bool basicLower = bounds[item.basic][0].usable();
            const bool basicUpper = bounds[item.basic][1].usable();
            int missingMinimum = 0, missingMaximum = 0;
            for (const auto& entry : row.entries) {
                if (exhausted()) return accepted;
                if (entry.coeff == 0) continue;
                const auto& variable = bounds[entry.col];
                const size_t minSide = entry.coeff > 0 ? 0 : 1;
                missingMinimum += !variable[minSide].usable();
                missingMaximum += !variable[1 - minSide].usable();
                if (missingMinimum > 0 && missingMaximum > 0 &&
                    (!basicLower || missingMaximum > 1) &&
                    (!basicUpper || missingMinimum > 1)) {
                    snapshot->insufficientBounds = true;
                    if (statistics) ++statistics->unproductiveSnapshots;
                    break;
                }
            }
            if (!snapshot->insufficientBounds) {
                contributions.reserve(row.entries.size());
                for (const auto& entry : row.entries) {
                    if (exhausted()) return accepted;
                    const auto& variable = bounds[entry.col];
                    const size_t minSide = entry.coeff > 0 ? 0 : 1;
                    contributions.push_back({Contribution(variable[minSide], entry.coeff),
                                             Contribution(variable[1 - minSide], entry.coeff)});
                    snapshot->minimum.add(contributions.back()[0]);
                    snapshot->maximum.add(contributions.back()[1]);
                    if (statistics) ++statistics->termPairs;
                }
            }
        } else if (statistics) ++statistics->snapshotHits;
        if (snapshot->insufficientBounds) continue;
        const auto& contributions = snapshot->contributions;
        const auto& minimum = snapshot->minimum;
        const auto& maximum = snapshot->maximum;

        const auto& forward = item.lower ? minimum : maximum;
        if (forward.missing == 0)
            publish(item.basic, item.lower, DeltaRational(row.rhs) + forward.sum,
                    forward, nullptr, {});

        const auto basic = bounds[item.basic][item.lower ? 0 : 1];
        if (!basic.usable()) continue;
        // s >= L always subtracts the MAXIMUM of the other terms;
        // s <= U always subtracts their MINIMUM. The target coefficient
        // controls the final inequality direction only, after division.
        const auto& backward = item.lower ? maximum : minimum;
        const size_t contributionSide = item.lower ? 1 : 0;
        for (size_t index = 0; index < row.entries.size() && !exhausted(); ++index) {
            const auto& entry = row.entries[index];
            if (entry.coeff == 0) continue;
            const auto& excluded = contributions[index][contributionSide];
            if (backward.missing != (excluded.available ? 0u : 1u)) continue;
            DeltaRational others = backward.sum;
            if (excluded.available) others -= excluded.value;
            const auto value = (*basic.value - DeltaRational(row.rhs) - others) / entry.coeff;
            const bool lower = item.lower ? entry.coeff > 0 : entry.coeff < 0;
            if (!publish(entry.col, lower, value, backward, &excluded, basic.reasons)) continue;
            // Only rows incident to the changed non-basic variable can learn
            // something new. Pending visits coalesce, so the queue is bounded
            // by two entries per tableau row.
            for (const auto& incident : gs.tableau().col(entry.col).entries) {
                const int affected = gs.tableau().row(incident.row).basicVar;
                if (affected >= 0) { enqueue(affected, true); enqueue(affected, false); }
            }
        }
    }
    return accepted;
}

} // namespace xolver
