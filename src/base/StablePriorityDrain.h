#pragma once

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <deque>
#include <functional>
#include <type_traits>
#include <utility>
#include <vector>

namespace xolver {

// Drain append-only pending work in priority order, retaining FIFO order for
// equal keys. Producers keep appending to the original deque. Keys of queued
// items must remain unchanged while the drain is alive. Consumed slots may
// remain until compaction. On scope exit, including exception unwinding, only
// unconsumed items remain, in their original insertion order. Do not otherwise
// mutate or inspect the deque during a drain; Compare is a strict weak order.
template<class T, class KeyOf, class Compare = std::less<>>
class StablePriorityDrain {
    static_assert(std::is_nothrow_move_constructible_v<T>);
    static_assert(std::is_nothrow_move_assignable_v<T>);
    static_assert(std::is_nothrow_destructible_v<T>);
    using Key = std::remove_cvref_t<std::invoke_result_t<KeyOf&, const T&>>;
    static_assert(std::is_nothrow_destructible_v<Key>);
    struct Entry {
        std::size_t position;
        Key key;
    };

    std::deque<T>& pending_;
    KeyOf keyOf_;
    Compare compare_;
    std::vector<Entry> heap_;
    std::vector<unsigned char> consumed_;
    std::size_t indexed_ = 0;
    std::size_t retired_ = 0;

    bool after(const Entry& a, const Entry& b) {
        if (std::invoke(compare_, a.key, b.key)) return false;
        if (std::invoke(compare_, b.key, a.key)) return true;
        return a.position > b.position;
    }

    void synchronize() {
        const auto count = pending_.size();
        assert(count >= indexed_);
        if (count == indexed_) return;
        try {
            consumed_.resize(count, 0);
            const auto order = [this](const Entry& a, const Entry& b) { return after(a, b); };
            if (heap_.empty()) {
                for (auto i = indexed_; i < count; ++i)
                    heap_.push_back({i, std::invoke(keyOf_, std::as_const(pending_[i]))});
                std::make_heap(heap_.begin(), heap_.end(), order);
            } else {
                for (auto i = indexed_; i < count; ++i) {
                    heap_.push_back({i, std::invoke(keyOf_, std::as_const(pending_[i]))});
                    std::push_heap(heap_.begin(), heap_.end(), order);
                }
            }
            indexed_ = count;
        } catch (...) {
            compact();
            throw;
        }
    }

    void compact() noexcept {
        if (retired_ != 0) {
            std::size_t write = 0;
            for (std::size_t read = 0; read < pending_.size(); ++read) {
                if (read < consumed_.size() && consumed_[read]) continue;
                if (write != read) pending_[write] = std::move(pending_[read]);
                ++write;
            }
            pending_.erase(pending_.begin() + static_cast<std::ptrdiff_t>(write), pending_.end());
        }
        heap_.clear();
        consumed_.clear();
        indexed_ = retired_ = 0;
    }

public:
    explicit StablePriorityDrain(std::deque<T>& pending, KeyOf keyOf, Compare compare = {})
        : pending_(pending), keyOf_(std::move(keyOf)), compare_(std::move(compare)) {}
    StablePriorityDrain(const StablePriorityDrain&) = delete;
    StablePriorityDrain& operator=(const StablePriorityDrain&) = delete;
    ~StablePriorityDrain() noexcept { compact(); }

    bool empty() const noexcept { return pending_.size() == retired_; }

    T pop() {
        synchronize();
        assert(!heap_.empty());
        try {
            std::pop_heap(heap_.begin(), heap_.end(),
                          [this](const Entry& a, const Entry& b) { return after(a, b); });
        } catch (...) {
            compact();
            throw;
        }
        const auto position = heap_.back().position;
        heap_.pop_back();
        T value = std::move(pending_[position]);
        consumed_[position] = 1;
        ++retired_;
        // Reclaim holes when they outnumber remaining work. Each compaction
        // is paid for by retired items, keeping storage and rebuilding linear.
        if (retired_ >= pending_.size() - retired_) compact();
        return value;
    }
};

} // namespace xolver
