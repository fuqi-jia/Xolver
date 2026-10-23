#pragma once
#include "base/SolveClock.h"
#include <cstddef>
#include <limits>
#include <stdexcept>

namespace xolver::quantifiers {
struct Limits {
    std::size_t work = 2000000;
    std::size_t nodes = 250000;
    std::size_t depth = 512;
    std::size_t polynomials = 8000;
    int projectionMatrix = 16;
};
struct Exhausted : std::runtime_error { using std::runtime_error::runtime_error; };
struct Unsupported : std::runtime_error { using std::runtime_error::runtime_error; };
class Resources {
    std::size_t nesting_ = 0;
public:
    Limits limits;
    std::size_t work = 0;
    explicit Resources(Limits l = {}) : limits(l) {}
    void tick(std::size_t amount = 1) {
        if (amount > std::numeric_limits<std::size_t>::max() - work ||
            (limits.work && (work > limits.work || amount > limits.work - work)))
            throw Exhausted("quantifier work budget exhausted");
        work += amount;
        if (wall::hasDeadline() && wall::remainingMs() == 0)
            throw Exhausted("quantifier wall-clock budget exhausted");
    }
    void nodes(std::size_t count) {
        if (limits.nodes && count > limits.nodes)
            throw Exhausted("quantifier node budget exhausted");
    }
    class Frame {
        Resources& owner_;
    public:
        explicit Frame(Resources& owner) : owner_(owner) {
            owner_.tick();
            if (owner_.limits.depth && owner_.nesting_ >= owner_.limits.depth)
                throw Exhausted("quantifier recursion budget exhausted");
            ++owner_.nesting_;
        }
        ~Frame() { --owner_.nesting_; }
        Frame(const Frame&) = delete;
    };
};
}
