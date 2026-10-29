#include "parallel/ThreadPool.h"
#include <doctest/doctest.h>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <memory>
#include <mutex>
#include <set>
#include <stdexcept>
#include <thread>
#include <vector>

using namespace xolver::parallel;

TEST_CASE("parallel: typed tasks, move-only arguments and exception recovery") {
    ThreadPool pool(2);
    Executor& executor = pool;
    auto value = executor.submit([](std::unique_ptr<int> p) { return *p + 1; }, std::make_unique<int>(41));
    CHECK(value.get() == 42);
    auto failure = executor.submit([]() -> int { throw std::runtime_error("task failure"); });
    CHECK_THROWS_AS(failure.get(), std::runtime_error);
    int target = 0;
    executor.submit([](int& value) { value = 7; }, std::ref(target)).get();
    CHECK(target == 7);
    CHECK(executor.submit([] { return std::string("still running"); }).get() == "still running");
    pool.waitIdle();
}

TEST_CASE("parallel: bounded workers execute independent tasks concurrently") {
    ThreadPool pool(2);
    std::mutex mutex;
    std::condition_variable changed;
    std::set<std::thread::id> threads;
    bool release = false;
    auto task = [&] {
        std::unique_lock lock(mutex);
        threads.insert(std::this_thread::get_id());
        changed.notify_all();
        changed.wait(lock, [&] { return release; });
    };
    auto a = pool.submit(task), b = pool.submit(task);
    bool concurrent;
    {
        std::unique_lock lock(mutex);
        concurrent = changed.wait_for(lock, std::chrono::seconds(5), [&] { return threads.size() == 2; });
        release = true;
    }
    changed.notify_all();
    a.get(); b.get();
    CHECK(concurrent);
    CHECK(pool.concurrency() == 2);
}

TEST_CASE("parallel: close and destruction drain accepted work") {
    std::atomic<int> completed = 0;
    std::vector<std::future<void>> results;
    {
        ThreadPool pool(2);
        for (int i = 0; i < 20; ++i) results.push_back(pool.submit([&] { ++completed; }));
        pool.close();
        pool.close();
        CHECK_THROWS_AS(pool.submit([] {}), std::logic_error);
    }
    for (auto& result : results) result.get();
    CHECK(completed == 20);
}

TEST_CASE("parallel: invalid width and self-wait fail without deadlock") {
    CHECK_THROWS_AS(ThreadPool(0), std::invalid_argument);
    ThreadPool pool(1);
    auto selfWait = pool.submit([&] { pool.waitIdle(); });
    CHECK_THROWS_AS(selfWait.get(), std::logic_error);
    pool.waitIdle();
}
