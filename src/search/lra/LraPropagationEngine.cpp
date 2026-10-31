#include "search/lra/LraPropagationEngine.h"
#include <algorithm>
#include <array>
#include <chrono>
#include <deque>
#include <exception>
#include <map>
#include <optional>
#include <limits>
#include <unordered_map>

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

uint64_t sourceKey(SatLit literal) {
    return (static_cast<uint64_t>(literal.var) << 1) | literal.sign;
}

struct RowSnapshot {
    int basic = -1;
    uint64_t revision = 0, builtCall = 0, checkedCall = 0;
    bool valid = false, insufficientBounds = false;
    std::vector<std::array<Contribution, 2>> contributions;
    RowAggregate minimum, maximum;
    std::vector<std::pair<uint64_t, uint64_t>> sources;
    std::size_t weight = 0;
};

} // namespace

struct LraPropagationEngine::State {
    const GeneralSimplex* owner = nullptr;
    std::shared_ptr<const void> identity;
    std::vector<std::array<BoundInfo, 2>> inputs;
    std::unordered_map<uint64_t, uint64_t> sourceVersions;
    std::vector<std::unique_ptr<RowSnapshot>> rows;
    uint64_t call = 0;
    std::size_t weight = 0, evictionCursor = 0;
    static constexpr std::size_t maxWeight = 32768;

    void invalidate(int var, const GeneralSimplex& gs) {
        for (const auto& incident : gs.tableau().col(var).entries)
            if (rows[incident.row]) rows[incident.row]->valid = false;
    }

    void expire(const BoundInfo& input) {
        if (!input.bound.isFinite() || !input.reason) return;
        auto& version = sourceVersions[sourceKey(*input.reason)];
        if (version != std::numeric_limits<uint64_t>::max()) ++version;
    }

    RowSnapshot* retain(int row, std::size_t needed) {
        auto& slot = rows[row];
        if (slot && slot->weight == needed) return slot.get();
        if (slot) { weight -= slot->weight; slot.reset(); }
        if (needed > maxWeight) return nullptr;
        // Evict before exposing any row references. Publishing a bound only
        // invalidates snapshots; it never destroys the row being evaluated.
        while (weight + needed > maxWeight) {
            auto& victim = rows[evictionCursor];
            if (victim) { weight -= victim->weight; victim.reset(); }
            if (++evictionCursor == rows.size()) evictionCursor = 0;
        }
        slot = std::make_unique<RowSnapshot>();
        slot->weight = needed;
        weight += needed;
        return slot.get();
    }
};

LraPropagationEngine::LraPropagationEngine() = default;
LraPropagationEngine::~LraPropagationEngine() = default;
LraPropagationEngine::LraPropagationEngine(const LraPropagationEngine& other)
    : nextSeed_(other.nextSeed_) {}
LraPropagationEngine& LraPropagationEngine::operator=(const LraPropagationEngine& other) {
    if (this != &other) { state_.reset(); nextSeed_ = other.nextSeed_; }
    return *this;
}
LraPropagationEngine::LraPropagationEngine(LraPropagationEngine&&) noexcept = default;
LraPropagationEngine& LraPropagationEngine::operator=(LraPropagationEngine&&) noexcept = default;

std::vector<LraPropagationEngine::ExplainedBound>
LraPropagationEngine::propagateAll(const GeneralSimplex& gs,
                                  const PropagationBudget& budget,
                                  Statistics* statistics,
                                  const BoundConsumer& consume) try {
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

    const auto identity = gs.definitionIdentity();
    if (!state_ || !identity || state_->owner != &gs || state_->identity != identity ||
        state_->inputs.size() > static_cast<std::size_t>(gs.numVars()) ||
        state_->rows.size() > static_cast<std::size_t>(gs.numRows()) ||
        state_->call == std::numeric_limits<uint64_t>::max()) {
        state_ = std::make_unique<State>();
        state_->owner = &gs;
        state_->identity = identity;
    }
    // A consumer may invoke this engine recursively, including on another
    // simplex. Lease this invocation's cache so nested calls cannot replace
    // storage while the outer row still holds references into it.
    struct CacheLease {
        std::unique_ptr<State>& destination;
        std::unique_ptr<State> owned;
        std::size_t& resume;
        std::size_t nextSeed;
        int exceptions = std::uncaught_exceptions();
        ~CacheLease() {
            if (std::uncaught_exceptions() == exceptions) {
                destination = std::move(owned);
                resume = nextSeed;
            }
        }
    } lease{state_, std::move(state_), nextSeed_, nextSeed_};
    auto& cache = *lease.owned;
    ++cache.call;
    const auto oldSize = cache.inputs.size();
    cache.inputs.resize(gs.numVars());
    for (std::size_t var = oldSize; var < cache.inputs.size(); ++var)
        cache.inputs[var][0] = BoundInfo(BoundValue::negInf());
    cache.rows.resize(gs.numRows());

    // Every call starts with the actual primitive bounds. Retained arithmetic
    // carries its original SAT premises, whose versions also invalidate proofs
    // derived through other rows, even when their source is not incident here.
    std::vector<std::array<ExplainedEndpoint, 2>> bounds(gs.numVars());
    for (int var = 0; var < gs.numVars(); ++var) {
        const auto state = gs.varState(var);
        const BoundInfo* sources[] = {&state.lower, &state.upper};
        bool changed = false;
        for (size_t side = 0; side < 2; ++side) {
            auto& previous = cache.inputs[var][side];
            const auto& current = *sources[side];
            if (previous.bound.kind != current.bound.kind || previous.reason != current.reason ||
                (current.bound.isFinite() && previous.bound.value != current.bound.value)) {
                cache.expire(previous);
                cache.expire(current);
                previous = current;
                changed = true;
            }
            if (!sources[side]->bound.isFinite()) continue;
            auto& target = bounds[var][side];
            target.value = sources[side]->bound.value;
            if (sources[side]->reason) {
                target.reasons.push_back(*sources[side]->reason);
                target.explained = true;
            }
        }
        if (changed) {
            cache.invalidate(var, gs);
            if (statistics) ++statistics->changedInputs;
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
        auto seed = lease.nextSeed % seedCount;
        for (std::size_t count = 0; count < seedCount; ++count) {
            const int basic = gs.tableau().row(static_cast<int>(seed / 2)).basicVar;
            if (basic >= 0) enqueue(basic, seed % 2 == 0);
            if (++seed == seedCount) seed = 0;
        }
    }

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
        if (gs.basicRowOfVar(var) < 0) cache.invalidate(var, gs);
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
        lease.nextSeed = 2 * static_cast<std::size_t>(rowIndex) + (item.lower ? 1 : 2);
        if (lease.nextSeed == seedCount) lease.nextSeed = 0;
        const auto& row = gs.tableau().row(rowIndex);

        if (statistics) ++statistics->rowVisits;
        std::optional<RowSnapshot> temporary;
        RowSnapshot* snapshot = cache.retain(rowIndex, row.entries.size() + 1);
        if (!snapshot) { temporary.emplace(); snapshot = &*temporary; }
        if (snapshot->valid && snapshot->checkedCall != cache.call) {
            for (const auto& [source, version] : snapshot->sources) {
                const auto found = cache.sourceVersions.find(source);
                if (found == cache.sourceVersions.end() || found->second != version ||
                    version == std::numeric_limits<uint64_t>::max()) {
                    snapshot->valid = false;
                    if (statistics) ++statistics->expiredSources;
                    break;
                }
            }
            snapshot->checkedCall = cache.call;
        }
        if (!snapshot->valid || snapshot->basic != item.basic || snapshot->revision != row.version ||
            row.version == std::numeric_limits<uint64_t>::max()) {
            const auto weight = snapshot->weight;
            *snapshot = RowSnapshot{};
            snapshot->weight = weight;
            snapshot->basic = item.basic;
            snapshot->revision = row.version;
            snapshot->builtCall = snapshot->checkedCall = cache.call;
            auto& contributions = snapshot->contributions;
            if (statistics) ++statistics->rowSnapshots;
            // A forward bound needs every contribution; a backward bound can
            // omit only its target. Two unavailable endpoints in EACH extremum
            // rule out both directions, regardless of the basic variable's
            // bounds. Detect that before doing rational arithmetic or building
            // explanations. A new non-basic bound invalidates and requeues
            // incident rows, so this cannot hide a later deduction.
            int missingMinimum = 0, missingMaximum = 0;
            for (const auto& entry : row.entries) {
                if (exhausted()) return accepted;
                if (entry.coeff == 0) continue;
                const auto& variable = bounds[entry.col];
                const size_t minSide = entry.coeff > 0 ? 0 : 1;
                missingMinimum += !variable[minSide].usable();
                missingMaximum += !variable[1 - minSide].usable();
                if (missingMinimum > 1 && missingMaximum > 1) {
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
            for (const auto* aggregate : {&snapshot->minimum, &snapshot->maximum}) {
                for (const auto& [reason, count] : aggregate->reasonCounts) {
                    const auto key = sourceKey(reason);
                    snapshot->sources.emplace_back(key, cache.sourceVersions.at(key));
                }
            }
            std::sort(snapshot->sources.begin(), snapshot->sources.end());
            snapshot->sources.erase(std::unique(snapshot->sources.begin(), snapshot->sources.end()),
                                    snapshot->sources.end());
            snapshot->valid = true;
        } else if (statistics) {
            ++statistics->snapshotHits;
            if (snapshot->builtCall != cache.call) ++statistics->retainedSnapshotHits;
        }
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
} catch (...) {
    // In particular, a throwing consumer must not leave partially constructed
    // or partially synchronized proof state available to a subsequent call.
    state_.reset();
    throw;
}

} // namespace xolver
