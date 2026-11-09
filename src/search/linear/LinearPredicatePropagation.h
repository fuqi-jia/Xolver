#pragma once

#include "base/IncrementalContext.h"
#include "contracts/LinearFormKey.h"
#include "contracts/TheoryAtomTypes.h"
#include <deque>
#include <optional>
#include <unordered_map>

namespace xolver {

class TheoryAtomRegistry;
class TheoryAssignmentView;
class TheoryLemmaStorage;

// Explained interval propagation within the existing predicate vocabulary.
// No variables or atoms are allocated, including for equality endpoints.
class LinearPredicatePropagation {
public:
    void reset();
    void assertLit(const TheoryAtomRegistry& registry, const TheoryAtomRecord& atom,
                   SatLit literal, int level);
    void backtrackToLevel(int level);
    std::optional<TheoryCheckResult> check(const TheoryAtomRegistry& registry,
        const TheoryAssignmentView* assignment, TheoryLemmaStorage& lemmas);

private:
    static constexpr size_t kNoFamily = static_cast<size_t>(-1);
    struct Atom {
        size_t family;
        Relation relation;
        mpq_class endpoint;
        size_t version;
    };
    struct Family {
        std::vector<SatVar> atoms;
        bool dirty = false;
        size_t nextDirty = kNoFamily;
    };
    struct Assertion {
        SatLit literal;
        int level;
        size_t family, version;
    };
    struct AssertionKey {
        SatVar operator()(const Assertion& entry) const { return entry.literal.var; }
    };
    struct Inference {
        std::vector<SatLit> reasons;
        std::optional<SatLit> conclusion;
    };
    using Trail = incremental::IndexedContext<Assertion, AssertionKey>;
    Trail trail_;
    size_t seenRecords_ = 0;
    // Coordinate names are local to a theory owner. Reuse the algorithm across
    // domains without equating independently owned same-name coordinates.
    std::unordered_map<TheoryId,
        std::unordered_map<LinearFormKey, size_t, LinearFormKeyHash>> familyIndex_;
    std::vector<Family> families_;
    std::unordered_map<SatVar, Atom> atoms_;
    size_t dirtyHead_ = kNoFamily, dirtyTail_ = kNoFamily;
    std::deque<Inference> pending_;

    void synchronize(const TheoryAtomRegistry& registry);
    void markDirty(size_t family) noexcept;
    std::optional<bool> value(SatVar variable, const TheoryAssignmentView* assignment) const;
    void derive(size_t family, const TheoryAssignmentView* assignment);
    std::optional<TheoryCheckResult> takePending(const TheoryAssignmentView* assignment,
                                               TheoryLemmaStorage& lemmas);
};

} // namespace xolver
