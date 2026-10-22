#pragma once
#include "xolver/SeparationLogic.h"
#include "base/SolveClock.h"
#include <stdexcept>

namespace xolver::sl::detail {
using Record = std::vector<ConcreteField>;
using Heap = std::map<uint64_t, Record>;
struct Stop : std::runtime_error { using std::runtime_error::runtime_error; };
struct Work {
    Limits limits;
    uint64_t steps = 0;
    void tick(uint64_t amount = 1) {
        if (amount > limits.maxSteps - steps) throw Stop("separation logic work limit");
        steps += amount;
        if (wall::hasDeadline() && wall::remainingMs() == 0)
            throw Stop("separation logic wall-clock limit");
    }
};
struct Prepared {
    Formula formula;
    std::vector<std::size_t> width;
    std::vector<Location> symbols;
    std::vector<bool> reachable;
};
// Validates the typed, acyclic input and canonicalizes exact integer literals.
Prepared prepare(const Formula&, Work&);
struct Vocabulary {
    std::vector<uint64_t> addresses; // non-nil values of mentioned locations
    std::vector<Record> records;    // mentioned records plus one fresh record
};
Vocabulary vocabulary(const Prepared&, const std::map<Location, uint64_t>&, Work&);
Heap canonicalHeap(const Prepared&, const Model&, Work&);
Record instantiate(const PointsTo&, const std::map<Location, uint64_t>&);
// Pick count fresh addresses, excluding the stack and the entire current heap.
std::vector<uint64_t> freshAddresses(const Vocabulary&, const Heap&, std::size_t, Work&);
} // namespace xolver::sl::detail
