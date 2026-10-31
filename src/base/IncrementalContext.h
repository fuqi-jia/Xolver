#pragma once

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <unordered_map>
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
    uint64_t prefixRevision_ = 0;
    void invalidatePrefix() noexcept {
        if (prefixRevision_ != std::numeric_limits<uint64_t>::max()) ++prefixRevision_;
    }

    bool orderedLevels() const {
        return std::is_sorted(entries_.begin(), entries_.end(),
            [](const auto& a, const auto& b) { return levelOf(a) < levelOf(b); });
    }

public:
    Context() = default;
    Context(const Context& other) : entries_(other.entries_), ordered_(other.ordered_) {}
    Context(Context&& other) noexcept
        : entries_(std::move(other.entries_)), ordered_(other.ordered_) { other.invalidatePrefix(); }
    Context& operator=(const Context& other) {
        if (this != &other) {
            invalidatePrefix(); ordered_ = false;
            entries_ = other.entries_; ordered_ = other.ordered_;
        }
        return *this;
    }
    Context& operator=(Context&& other) noexcept {
        if (this != &other) {
            invalidatePrefix(); other.invalidatePrefix();
            entries_ = std::move(other.entries_); ordered_ = other.ordered_;
        }
        return *this;
    }
    // Appends preserve every previous entry. All other source mutations,
    // including assignment/restore and moving out, invalidate prefix reuse.
    // Saturation disables reuse rather than allowing a generation to alias.
    std::optional<uint64_t> retainedPrefixRevision() const noexcept {
        if (prefixRevision_ == std::numeric_limits<uint64_t>::max()) return std::nullopt;
        return prefixRevision_;
    }
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
        invalidatePrefix();
        const bool ordered = ordered_ &&
            (index == 0 || levelOf(entries_[index - 1]) <= levelOf(entry)) &&
            (index + 1 == size() || levelOf(entry) <= levelOf(entries_[index + 1]));
        ordered_ = false;
        previous = std::move(entry);
        ordered_ = ordered;
    }
    void clear() { invalidatePrefix(); entries_.clear(); ordered_ = true; }

    // Explicit prefix retention also supports clients whose withdrawal policy
    // deliberately differs from level filtering.
    void truncate(size_t count) {
        if (count > size()) throw std::out_of_range("context prefix exceeds size");
        if (count != size()) invalidatePrefix();
        while (size() > count) entries_.pop_back();
    }

    // Explicit owning snapshots support application push/pop, including source
    // replacement. Ordinary decision backtracking never copies retained entries.
    Snapshot snapshot() const { return Snapshot(entries_, ordered_); }
    void restore(Snapshot saved) {
        invalidatePrefix();
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
        invalidatePrefix();
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

// Optional lookup acceleration for level-tagged sources. KeyOf and LevelOf
// are stateless projections; neither SAT identities nor theory policy belong
// here. Duplicate keys resolve to the first retained source, matching an
// ordered linear search. Clients that only append/iterate never build an index.
template<class Entry, class KeyOf, class LevelOf = MemberLevel>
class IndexedContext {
    static_assert(std::is_empty_v<KeyOf>);
    using Sources = Context<Entry, LevelOf>;
    using Key = std::remove_cvref_t<decltype(KeyOf{}(std::declval<const Entry&>()))>;
    using Level = std::remove_cvref_t<decltype(LevelOf{}(std::declval<const Entry&>()))>;
    Sources sources_;
    mutable std::unordered_map<Key, size_t> index_;
    mutable bool indexed_ = false;

    void ensureIndex() const {
        if (indexed_) return;
        index_.clear();
        if (size() > index_.bucket_count() * index_.max_load_factor()) index_.reserve(size());
        for (size_t i = 0; i < size(); ++i) index_.emplace(KeyOf{}(sources_[i]), i);
        indexed_ = true;
    }

    void withdrawIndex(const Entry& entry, size_t position) {
        if (!indexed_) return;
        const auto found = index_.find(KeyOf{}(entry));
        if (found != index_.end() && found->second == position) index_.erase(found);
    }

public:
    using Withdrawal = typename Sources::Withdrawal;
    using BacktrackResult = typename Sources::BacktrackResult;
    using Snapshot = typename Sources::Snapshot;
    std::optional<uint64_t> retainedPrefixRevision() const noexcept {
        return sources_.retainedPrefixRevision();
    }

    const std::vector<Entry>& entries() const { return sources_.entries(); }
    auto begin() const { return sources_.begin(); }
    auto end() const { return sources_.end(); }
    size_t size() const { return sources_.size(); }
    bool empty() const { return sources_.empty(); }
    const Entry& operator[](size_t position) const { return sources_[position]; }
    const Entry& back() const { return sources_.back(); }
    void reserve(size_t count) {
        sources_.reserve(count);
        if (indexed_) index_.reserve(count);
    }

    std::optional<size_t> find(const Key& key) const {
        ensureIndex();
        const auto found = index_.find(key);
        if (found == index_.end()) return std::nullopt;
        return found->second;
    }

    void append(Entry entry) {
        if (!indexed_) { sources_.append(std::move(entry)); return; }
        const auto [position, inserted] = index_.emplace(KeyOf{}(entry), size());
        try {
            sources_.append(std::move(entry));
        } catch (...) {
            if (inserted) index_.erase(position);
            throw;
        }
    }

    void replace(size_t position, Entry entry) {
        // Keys normally stay fixed on assignment replacement. A changed key
        // invalidates the lookup cache; rebuilding it also handles duplicates.
        if (position >= size()) throw std::out_of_range("context replacement exceeds size");
        if (indexed_ && KeyOf{}(sources_[position]) != KeyOf{}(entry)) indexed_ = false;
        try {
            sources_.replace(position, std::move(entry));
        } catch (...) {
            indexed_ = false;
            throw;
        }
    }

    void truncate(size_t count) {
        if (count > size()) throw std::out_of_range("context prefix exceeds size");
        for (size_t i = size(); i > count; --i) withdrawIndex(sources_[i - 1], i - 1);
        sources_.truncate(count);
    }

    void clear() { sources_.clear(); index_.clear(); indexed_ = false; }
    Snapshot snapshot() const { return sources_.snapshot(); }
    void restore(Snapshot saved) {
        sources_.restore(std::move(saved));
        index_.clear();
        indexed_ = false;
    }

    template<class Undo>
    BacktrackResult backtrack(Level target, Undo&& undo) {
        const auto result = sources_.backtrack(target, [&](const Entry& entry) {
            withdrawIndex(entry, size() - 1);
            undo(entry);
        });
        if (result.kind == Withdrawal::Filtered) indexed_ = false;
        return result;
    }
    BacktrackResult backtrack(Level target) {
        return backtrack(target, [](const Entry&) noexcept {});
    }
};

} // namespace xolver::incremental
