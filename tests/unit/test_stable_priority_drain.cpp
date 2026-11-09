#include <doctest/doctest.h>
#include "base/StablePriorityDrain.h"

#include <algorithm>
#include <memory>
#include <random>
#include <stdexcept>
#include <string>

using namespace xolver;

namespace {
struct Task {
    int priority, id;
    bool operator==(const Task&) const = default;
};

Task removeMinimum(std::vector<Task>& tasks) {
    const auto first = std::min_element(tasks.begin(), tasks.end(),
        [](const Task& a, const Task& b) { return a.priority < b.priority; });
    const auto result = *first;
    tasks.erase(first);
    return result;
}
}

TEST_CASE("priority drain: appended work and interrupted scopes match stable linear selection") {
    std::deque<Task> tasks;
    std::vector<Task> expected;
    std::minstd_rand random(931752);
    int nextId = 0;
    const auto append = [&]() {
        const Task task{static_cast<int>(random() % 23) - 11, nextId++};
        tasks.push_back(task);
        expected.push_back(task);
    };
    for (int i = 0; i < 120; ++i) append();
    for (int phase = 0; phase < 9; ++phase) {
        {
            StablePriorityDrain drain(tasks, &Task::priority);
            for (int step = 0; step < 90; ++step) {
                for (unsigned i = 0, count = random() % 4; i < count; ++i) append();
                REQUIRE(drain.empty() == expected.empty());
                if (!expected.empty()) CHECK(drain.pop() == removeMinimum(expected));
            }
            // This last append is deliberately not indexed before unwinding.
            append();
        }
        CHECK(std::vector<Task>(tasks.begin(), tasks.end()) == expected);
    }
    {
        StablePriorityDrain drain(tasks, &Task::priority);
        while (!drain.empty()) CHECK(drain.pop() == removeMinimum(expected));
        CHECK(expected.empty());
    }
    CHECK(tasks.empty());
}

TEST_CASE("priority drain: an exceptional consumer retains every unconsumed task in insertion order") {
    std::deque<Task> tasks{{4, 1}, {2, 2}, {8, 3}, {2, 4}};
    CHECK_THROWS_AS(([&]() {
        StablePriorityDrain drain(tasks, &Task::priority);
        CHECK(drain.pop() == Task{2, 2});
        tasks.push_back({-1, 5});
        throw std::runtime_error("consumer failed");
    }()), std::runtime_error);
    const std::vector<Task> remaining{{4, 1}, {8, 3}, {2, 4}, {-1, 5}};
    CHECK(std::vector<Task>(tasks.begin(), tasks.end()) == remaining);
}

TEST_CASE("priority drain: failed key extraction discards the index and permits a fresh attempt") {
    std::deque<Task> tasks;
    std::vector<Task> expected;
    for (int i = 0; i < 20; ++i) {
        tasks.push_back({i % 5, i});
        expected.push_back(tasks.back());
    }
    bool reject = false;
    auto key = [&](const Task& task) {
        if (reject && task.id == 20) throw std::runtime_error("key unavailable");
        return task.priority;
    };
    {
        StablePriorityDrain drain(tasks, key);
        REQUIRE(drain.pop() == removeMinimum(expected));
        tasks.push_back({-3, 20});
        expected.push_back(tasks.back());
        reject = true;
        CHECK_THROWS_AS(drain.pop(), std::runtime_error);
        CHECK(std::vector<Task>(tasks.begin(), tasks.end()) == expected);
        reject = false;
        while (!drain.empty()) CHECK(drain.pop() == removeMinimum(expected));
    }
    CHECK(expected.empty());
    CHECK(tasks.empty());
}

TEST_CASE("priority drain: a failed comparison preserves queued payloads and allows recovery") {
    std::deque<Task> tasks;
    std::vector<Task> expected;
    for (int i = 0; i < 25; ++i) {
        tasks.push_back({24 - i, i});
        expected.push_back(tasks.back());
    }
    bool reject = false;
    auto less = [&](int a, int b) {
        if (reject) throw std::runtime_error("comparison failed");
        return a < b;
    };
    {
        StablePriorityDrain drain(tasks, &Task::priority, less);
        REQUIRE(drain.pop() == removeMinimum(expected));
        reject = true;
        CHECK_THROWS_AS(drain.pop(), std::runtime_error);
        CHECK(std::vector<Task>(tasks.begin(), tasks.end()) == expected);
        reject = false;
        while (!drain.empty()) CHECK(drain.pop() == removeMinimum(expected));
    }
    CHECK(expected.empty());
    CHECK(tasks.empty());
}

TEST_CASE("priority drain: noncopyable payload ownership survives repeated indexing and compaction") {
    struct OwnedTask {
        int priority;
        std::unique_ptr<int> value;
    };
    std::deque<OwnedTask> tasks;
    for (int i = 0; i < 1024; ++i) tasks.push_back({i % 17, std::make_unique<int>(i)});
    std::vector<bool> seen(1024);
    int previousPriority = -1, previousId = -1;
    {
        StablePriorityDrain drain(tasks, &OwnedTask::priority);
        while (!drain.empty()) {
            auto task = drain.pop();
            REQUIRE(task.value);
            const auto id = *task.value;
            REQUIRE(id >= 0);
            REQUIRE(id < static_cast<int>(seen.size()));
            CHECK_FALSE(seen[id]);
            seen[id] = true;
            CHECK(task.priority >= previousPriority);
            if (task.priority == previousPriority) CHECK(id > previousId);
            previousPriority = task.priority;
            previousId = id;
        }
    }
    CHECK(tasks.empty());
    CHECK(std::all_of(seen.begin(), seen.end(), [](bool value) { return value; }));
}

TEST_CASE("priority drain: large batches avoid a quadratic number of comparisons") {
    constexpr std::size_t count = 4096;
    std::deque<Task> tasks;
    for (std::size_t i = 0; i < count; ++i)
        tasks.push_back({static_cast<int>(count - i), static_cast<int>(i)});
    std::size_t comparisons = 0;
    auto less = [&](int a, int b) { ++comparisons; return a < b; };
    {
        StablePriorityDrain drain(tasks, &Task::priority, less);
        for (std::size_t i = 0; i < count; ++i) {
            REQUIRE_FALSE(drain.empty());
            CHECK(drain.pop().priority == static_cast<int>(i + 1));
        }
        CHECK(drain.empty());
    }
    CHECK(tasks.empty());
    CHECK(comparisons < 128 * count);
}

TEST_CASE("priority drain: custom ordering and nonintegral keys retain FIFO ties") {
    struct NamedTask { std::string key; int id; };
    std::deque<NamedTask> tasks{{"a", 0}, {"z", 1}, {"m", 2}, {"z", 3}};
    std::vector<int> ids;
    {
        StablePriorityDrain drain(tasks, &NamedTask::key, std::greater<>{});
        while (!drain.empty()) ids.push_back(drain.pop().id);
        CHECK(drain.empty());
        tasks.push_back({"z", 4});
        REQUIRE_FALSE(drain.empty());
        ids.push_back(drain.pop().id);
    }
    CHECK(ids == std::vector<int>{1, 3, 2, 0, 4});
    CHECK(tasks.empty());
}
