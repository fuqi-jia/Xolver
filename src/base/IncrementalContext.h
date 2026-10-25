#pragma once

#include <algorithm>
#include <cstddef>
#include <type_traits>
#include <utility>
#include <vector>

namespace xolver::incremental {

struct MemberLevel {
    template<class Entry> auto operator()(const Entry& entry) const { return entry.level; }
};

// Owns level-tagged sources, independently of SAT literals or theory caches.
// Mutation goes through this interface so the ordered-level fast path cannot
// become stale. LevelOf is a pure, stateless projection; entries are read-only.
template<class Entry, class LevelOf = MemberLevel>
class Context {
    static_assert(std::is_empty_v<LevelOf>);
    using Level = std::remove_cvref_t<decltype(LevelOf{}(std::declval<const Entry&>()))>;
    static auto levelOf(const Entry& entry) { return LevelOf{}(entry); }
    std::vector<Entry> entries_;
    bool ordered_ = true;

    bool orderedLevels() const {
        return std::is_sorted(entries_.begin(), entries_.end(),
            [](const auto& a, const auto& b) { return levelOf(a) < levelOf(b); });
    }

public:
    enum class Withdrawal { None, Suffix, Filtered };
    struct BacktrackResult {
        Withdrawal kind;
        size_t firstChanged, removed;
        bool changed() const { return kind != Withdrawal::None; }
    };
    class Snapshot {
        friend class Context;
        std::vector<Entry> entries_;
        bool ordered_ = true;
        Snapshot(const std::vector<Entry>& entries, bool ordered) : entries_(entries), ordered_(ordered) {}
    public:
        Snapshot() = default;
    };

    const std::vector<Entry>& entries() const { return entries_; }
    auto begin() const { return entries_.begin(); }
    auto end() const { return entries_.end(); }
    size_t size() const { return entries_.size(); }
    bool empty() const { return entries_.empty(); }
    const Entry& operator[](size_t index) const { return entries_[index]; }
    const Entry& back() const { return entries_.back(); }
    void reserve(size_t count) { entries_.reserve(count); }

    void append(Entry entry) {
        const bool ordered = ordered_ && (empty() || levelOf(back()) <= levelOf(entry));
        ordered_ = false;
        entries_.push_back(std::move(entry));
        ordered_ = ordered;
    }
    void replace(size_t index, Entry entry) {
        auto& previous = entries_.at(index);
        const bool ordered = ordered_ &&
            (index == 0 || levelOf(entries_[index - 1]) <= levelOf(entry)) &&
            (index + 1 == size() || levelOf(entry) <= levelOf(entries_[index + 1]));
        ordered_ = false;
        previous = std::move(entry);
        ordered_ = ordered;
    }
    void clear() { entries_.clear(); ordered_ = true; }

    // Explicit owning snapshots support application push/pop, including source
    // replacement. Ordinary decision backtracking never copies retained entries.
    Snapshot snapshot() const { return Snapshot(entries_, ordered_); }
    void restore(Snapshot saved) {
        entries_.swap(saved.entries_);
        ordered_ = saved.ordered_;
    }

    // Undo receives each suffix entry in reverse order, before its destruction.
    // It must not throw or reenter/mutate this context. With interior removals,
    // no undo is called: stable filtering returns Filtered so the caller can
    // rebuild its derived caches. Root-level restart policy belongs to callers.
    template<class Undo>
    BacktrackResult backtrack(Level target, Undo&& undo) {
        const auto withdrawn = [&](const Entry& entry) { return levelOf(entry) > target; };
        auto first = ordered_
            ? std::upper_bound(entries_.begin(), entries_.end(), target,
                [](const Level& level, const Entry& entry) { return level < levelOf(entry); })
            : std::find_if(entries_.begin(), entries_.end(), withdrawn);
        const size_t retained = static_cast<size_t>(first - entries_.begin());
        if (first == entries_.end()) return {Withdrawal::None, retained, 0};
        const size_t previous = size();
        if (ordered_ || std::all_of(first, entries_.end(), withdrawn)) {
            while (size() > retained) {
                undo(back());
                entries_.pop_back();
            }
            if (!ordered_) ordered_ = orderedLevels();
            return {Withdrawal::Suffix, retained, previous - size()};
        }
        ordered_ = false;
        entries_.erase(std::remove_if(first, entries_.end(), withdrawn), entries_.end());
        ordered_ = orderedLevels();
        return {Withdrawal::Filtered, retained, previous - size()};
    }
    BacktrackResult backtrack(Level target) {
        return backtrack(target, [](const Entry&) noexcept {});
    }
};

} // namespace xolver::incremental
