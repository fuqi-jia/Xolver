#include <doctest/doctest.h>
#include "base/IncrementalContext.h"
#include <memory>
#include <random>
#include <stdexcept>
#include <string>

using namespace xolver;

namespace {
struct Entry {
    int level, id;
    std::string text;
    bool operator==(const Entry&) const = default;
};
}

TEST_CASE("incremental context: arbitrary replacements and nested snapshots agree with independent level filtering") {
    using Context = incremental::Context<Entry>;
    Context context;
    std::vector<Entry> expected;
    std::vector<std::pair<Context::Snapshot, std::vector<Entry>>> scopes;
    std::minstd_rand random(291031);
    int next = 0;
    for (int step = 0; step < 1000; ++step) {
        CAPTURE(step);
        const auto operation = random() % 6;
        if (operation == 0 || expected.empty()) {
            Entry entry{static_cast<int>(random() % 9), ++next, "owned-" + std::to_string(next)};
            expected.push_back(entry);
            context.append(entry);
            entry.text = "caller-mutated";
        } else if (operation == 1) {
            const auto index = random() % expected.size();
            Entry entry{static_cast<int>(random() % 9), ++next, "replacement-" + std::to_string(next)};
            expected[index] = entry;
            context.replace(index, std::move(entry));
        } else if (operation == 2) {
            const int target = random() % 9;
            std::vector<Entry> kept;
            size_t firstRemoved = expected.size();
            for (size_t i = 0; i < expected.size(); ++i) {
                if (expected[i].level <= target) kept.push_back(expected[i]);
                else firstRemoved = std::min(firstRemoved, i);
            }
            const bool suffix = std::none_of(expected.begin() + firstRemoved, expected.end(),
                [&](const Entry& entry) { return entry.level <= target; });
            std::vector<int> undone;
            const auto result = context.backtrack(target, [&](const Entry& entry) { undone.push_back(entry.id); });
            CHECK(result.removed == expected.size() - kept.size());
            CHECK(result.firstChanged == firstRemoved);
            if (kept.size() == expected.size()) CHECK(result.kind == Context::Withdrawal::None);
            else if (suffix) {
                CHECK(result.kind == Context::Withdrawal::Suffix);
                std::vector<int> reverse;
                for (size_t i = expected.size(); i > firstRemoved; --i) reverse.push_back(expected[i - 1].id);
                CHECK(undone == reverse);
            } else {
                CHECK(result.kind == Context::Withdrawal::Filtered);
                CHECK(undone.empty());
            }
            expected = std::move(kept);
        } else if (operation == 3) {
            scopes.push_back({context.snapshot(), expected});
        } else if (operation == 4 && !scopes.empty()) {
            context.restore(std::move(scopes.back().first));
            expected = std::move(scopes.back().second);
            scopes.pop_back();
        } else {
            context.clear();
            expected.clear();
        }
        REQUIRE(context.size() == expected.size());
        CHECK(context.entries() == expected);
    }
}

TEST_CASE("incremental context: suffix withdrawal retains move-only parent storage and root sources") {
    struct MoveOnlyEntry { int level; std::unique_ptr<int> value; };
    incremental::Context<MoveOnlyEntry> context;
    for (int i = 0; i < 64; ++i) context.append({i / 8, std::make_unique<int>(i)});
    const auto* first = &context[0];
    const auto* payload = context[7].value.get();
    std::vector<int> undone;
    auto result = context.backtrack(0, [&](const auto& entry) { undone.push_back(*entry.value); });
    CHECK(result.removed == 56);
    CHECK(context.size() == 8);
    CHECK(&context[0] == first);
    CHECK(context[7].value.get() == payload);
    for (size_t i = 0; i < undone.size(); ++i) CHECK(undone[i] == 63 - static_cast<int>(i));
    CHECK_FALSE(context.backtrack(0).changed());
    CHECK_THROWS_AS(context.replace(99, {1, std::make_unique<int>(99)}), std::out_of_range);
    CHECK(context.size() == 8);
    context.replace(1, {3, std::make_unique<int>(99)});
    result = context.backtrack(0);
    CHECK(result.kind == decltype(context)::Withdrawal::Filtered);
    CHECK(context.size() == 7);
    CHECK(*context[1].value == 2);
}

TEST_CASE("incremental context: explicit snapshots restore overwritten sources with a custom level projection") {
    struct DomainEntry { unsigned depth; std::string value; };
    struct Depth { unsigned operator()(const DomainEntry& entry) const { return entry.depth; } };
    incremental::Context<DomainEntry, Depth> context;
    context.append({0, "parent"});
    const auto parent = context.snapshot();
    context.replace(0, {2, "child replacement"});
    context.append({1, "child source"});
    context.backtrack(1);
    REQUIRE(context.size() == 1);
    CHECK(context[0].value == "child source");
    context.restore(parent);
    REQUIRE(context.size() == 1);
    CHECK(context[0].value == "parent");
    context.clear();
    context.restore(parent);
    CHECK(context[0].value == "parent");
}
