#pragma once

#include <algorithm>
#include <cstddef>
#include <cstring>
#include <initializer_list>
#include <iterator>
#include <type_traits>
#include <utility>

namespace xolver {

/**
 * SmallVector: inline storage for N elements, heap fallback.
 *
 * Simplified version of LLVM's SmallVector for Stage A.
 */
template <typename T, size_t N = 4>
class SmallVector {
    static_assert(std::is_trivially_copyable_v<T> || std::is_nothrow_move_constructible_v<T>,
                  "T must be trivially copyable or nothrow move constructible");

public:
    using value_type = T;
    using size_type = size_t;
    using reference = T&;
    using const_reference = const T&;
    using pointer = T*;
    using const_pointer = const T*;
    using iterator = T*;
    using const_iterator = const T*;

    SmallVector() : begin_(inlineBuf_), end_(inlineBuf_), capacity_(inlineBuf_ + N) {}

    explicit SmallVector(size_t n) : SmallVector() {
        resize(n);
    }

    SmallVector(size_t n, const T& val) : SmallVector() {
        resize(n, val);
    }

    SmallVector(std::initializer_list<T> init) : SmallVector() {
        reserve(init.size());
        for (const auto& v : init) push_back(v);
    }

    template <typename It>
    SmallVector(It first, It last) : SmallVector() {
        for (; first != last; ++first) push_back(*first);
    }

    ~SmallVector() {
        clear();
        if (begin_ != inlineBuf_) delete[] begin_;
    }

    // Move
    SmallVector(SmallVector&& o) noexcept : SmallVector() {
        if (o.begin_ == o.inlineBuf_) {
            size_t n = o.size();
            reserve(n);
            for (size_t i = 0; i < n; ++i) {
                new (begin_ + i) T(std::move(o.begin_[i]));
            }
            end_ = begin_ + n;
            o.clear();
        } else {
            begin_ = o.begin_;
            end_ = o.end_;
            capacity_ = o.capacity_;
            o.begin_ = o.inlineBuf_;
            o.end_ = o.inlineBuf_;
            o.capacity_ = o.inlineBuf_ + N;
        }
    }

    SmallVector& operator=(SmallVector&& o) noexcept {
        if (this != &o) {
            clear();
            if (begin_ != inlineBuf_) delete[] begin_;
            if (o.begin_ == o.inlineBuf_) {
                begin_ = inlineBuf_;
                end_ = inlineBuf_;
                capacity_ = inlineBuf_ + N;
                size_t n = o.size();
                reserve(n);
                for (size_t i = 0; i < n; ++i) {
                    new (begin_ + i) T(std::move(o.begin_[i]));
                }
                end_ = begin_ + n;
                o.clear();
            } else {
                begin_ = o.begin_;
                end_ = o.end_;
                capacity_ = o.capacity_;
                o.begin_ = o.inlineBuf_;
                o.end_ = o.inlineBuf_;
                o.capacity_ = o.inlineBuf_ + N;
            }
        }
        return *this;
    }

    // Copy
    SmallVector(const SmallVector& o) : SmallVector() {
        reserve(o.size());
        for (const auto& v : o) push_back(v);
    }

    SmallVector& operator=(const SmallVector& o) {
        if (this != &o) {
            clear();
            reserve(o.size());
            for (const auto& v : o) push_back(v);
        }
        return *this;
    }

    // Element access
    reference operator[](size_t i) { return begin_[i]; }
    const_reference operator[](size_t i) const { return begin_[i]; }
    reference front() { return *begin_; }
    const_reference front() const { return *begin_; }
    reference back() { return *(end_ - 1); }
    const_reference back() const { return *(end_ - 1); }
    pointer data() { return begin_; }
    const_pointer data() const { return begin_; }

    // Iterators
    iterator begin() { return begin_; }
    iterator end() { return end_; }
    const_iterator begin() const { return begin_; }
    const_iterator end() const { return end_; }

    // Capacity
    size_t size() const { return static_cast<size_t>(end_ - begin_); }
    bool empty() const { return begin_ == end_; }
    size_t capacity() const { return static_cast<size_t>(capacity_ - begin_); }

    void reserve(size_t newCap) {
        if (newCap <= capacity()) return;
        grow(newCap);
    }

    void resize(size_t n) {
        if (n < size()) {
            for (size_t i = n; i < size(); ++i) begin_[i].~T();
            end_ = begin_ + n;
        } else if (n > size()) {
            reserve(n);
            for (size_t i = size(); i < n; ++i) {
                new (end_) T();
                ++end_;
            }
        }
    }

    void resize(size_t n, const T& val) {
        if (n < size()) {
            for (size_t i = n; i < size(); ++i) begin_[i].~T();
            end_ = begin_ + n;
        } else if (n > size()) {
            reserve(n);
            for (size_t i = size(); i < n; ++i) {
                new (end_) T(val);
                ++end_;
            }
        }
    }

    void clear() {
        for (size_t i = 0; i < size(); ++i) begin_[i].~T();
        end_ = begin_;
    }

    void push_back(const T& v) {
        if (end_ >= capacity_) grow(capacity() * 2);
        new (end_) T(v);
        ++end_;
    }

    void push_back(T&& v) {
        if (end_ >= capacity_) grow(capacity() * 2);
        new (end_) T(std::move(v));
        ++end_;
    }

    template <typename... Args>
    reference emplace_back(Args&&... args) {
        if (end_ >= capacity_) grow(capacity() * 2);
        new (end_) T(std::forward<Args>(args)...);
        return *end_++;
    }

    void pop_back() {
        if (!empty()) {
            --end_;
            end_->~T();
        }
    }

private:
    void grow(size_t newCap) {
        if (newCap < N * 2) newCap = N * 2;
        T* newBuf = new T[newCap];
        size_t n = size();
        for (size_t i = 0; i < n; ++i) {
            new (newBuf + i) T(std::move(begin_[i]));
            begin_[i].~T();
        }
        if (begin_ != inlineBuf_) delete[] begin_;
        begin_ = newBuf;
        end_ = begin_ + n;
        capacity_ = begin_ + newCap;
    }

    alignas(alignof(T)) char inlineStorage_[sizeof(T) * N];
    T* inlineBuf_ = reinterpret_cast<T*>(inlineStorage_);
    T* begin_;
    T* end_;
    T* capacity_;
};

template <typename T, size_t N>
bool operator==(const SmallVector<T,N>& a, const SmallVector<T,N>& b) {
    if (a.size() != b.size()) return false;
    for (size_t i = 0; i < a.size(); ++i) if (!(a[i] == b[i])) return false;
    return true;
}
template <typename T, size_t N>
bool operator<(const SmallVector<T,N>& a, const SmallVector<T,N>& b) {
    size_t n = a.size() < b.size() ? a.size() : b.size();
    for (size_t i = 0; i < n; ++i) {
        if (a[i] < b[i]) return true;
        if (b[i] < a[i]) return false;
    }
    return a.size() < b.size();
}

} // namespace xolver
