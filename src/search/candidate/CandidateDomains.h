#pragma once

#include <cstddef>
#include <limits>
#include <memory>
#include <stdexcept>
#include <utility>
#include <vector>

namespace xolver {

// One candidate attempt owns a pool. Capture ONE snapshot for an entire
// traversal, including its explanations. Suggestions do not change that
// snapshot. Publishing them starts a new traversal with fresh explanations;
// existing snapshots remain valid even after publication or owner destruction.
// Value equality is exact and supplied by the client's domain. Filtering,
// resource allocation and complete-model checking belong to that client.
template <typename Value>
class CandidateDomains {
    using Values = std::vector<std::vector<Value>>;

public:
    class Snapshot {
    public:
        const std::vector<Value>& values(size_t depth) const { return values_->at(depth); }
        size_t size() const { return values_->size(); }

    private:
        friend class CandidateDomains;
        explicit Snapshot(std::shared_ptr<const Values> values) : values_(std::move(values)) {}
        std::shared_ptr<const Values> values_;
    };

    explicit CandidateDomains(Values values)
        : published_(std::make_shared<const Values>(std::move(values))), pending_(published_->size()) {}

    Snapshot snapshot() const { return Snapshot(published_); }

    template <typename Tick>
    bool suggest(size_t depth, const Value& value, Tick&& tick) {
        auto& pending = pending_.at(depth);
        for (const auto& current : published_->at(depth)) {
            tick();
            if (current == value) return false;
        }
        for (const auto& current : pending) {
            tick();
            if (current == value) return false;
        }
        tick();
        pending.push_back(value);
        return true;
    }

    // Cancellation leaves both the published snapshot and pending suggestions
    // intact. No partially published domain can invalidate a search explanation.
    template <typename Tick>
    size_t refine(Tick&& tick) {
        size_t added = 0;
        for (const auto& pending : pending_) {
            if (pending.size() > std::numeric_limits<size_t>::max() - added)
                throw std::length_error("candidate domain size overflow");
            added += pending.size();
        }
        if (!added) return 0;
        Values next;
        next.reserve(published_->size());
        for (size_t depth = 0; depth < published_->size(); ++depth) {
            std::vector<Value> values;
            values.reserve(published_->at(depth).size() + pending_[depth].size());
            for (const auto& value : published_->at(depth)) { tick(); values.push_back(value); }
            for (const auto& value : pending_[depth]) { tick(); values.push_back(value); }
            next.push_back(std::move(values));
        }
        auto publication = std::make_shared<const Values>(std::move(next));
        tick();
        published_ = std::move(publication);
        for (auto& pending : pending_) pending.clear();
        return added;
    }

private:
    std::shared_ptr<const Values> published_;
    Values pending_;
};

} // namespace xolver
