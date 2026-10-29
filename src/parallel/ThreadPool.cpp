#include "parallel/ThreadPool.h"

#include <condition_variable>
#include <deque>
#include <mutex>
#include <stdexcept>
#include <thread>
#include <vector>

namespace xolver::parallel {

struct ThreadPool::State {
    std::mutex mutex;
    std::condition_variable ready, idle;
    std::deque<Task> tasks;
    std::vector<std::thread> workers;
    std::size_t active = 0;
    bool closed = false;
};

ThreadPool::ThreadPool(std::size_t workers) : state_(std::make_unique<State>()) {
    if (!workers) throw std::invalid_argument("thread pool needs at least one worker");
    state_->workers.reserve(workers);
    try {
        for (std::size_t i = 0; i < workers; ++i) {
            state_->workers.emplace_back([this] {
                auto& state = *state_;
                for (;;) {
                    Task task;
                    {
                        std::unique_lock lock(state.mutex);
                        state.ready.wait(lock, [&] { return state.closed || !state.tasks.empty(); });
                        if (state.tasks.empty()) return;
                        task = std::move(state.tasks.front());
                        state.tasks.pop_front();
                        ++state.active;
                    }
                    task(); // submit() wraps user exceptions in a packaged_task.
                    {
                        std::lock_guard lock(state.mutex);
                        --state.active;
                        if (state.tasks.empty() && !state.active) state.idle.notify_all();
                    }
                }
            });
        }
    } catch (...) {
        close();
        for (auto& worker : state_->workers) worker.join();
        throw;
    }
}

ThreadPool::~ThreadPool() {
    close();
    for (auto& worker : state_->workers) worker.join();
}

std::size_t ThreadPool::concurrency() const noexcept { return state_->workers.size(); }

void ThreadPool::enqueue(Task task) {
    {
        std::lock_guard lock(state_->mutex);
        if (state_->closed) throw std::logic_error("thread pool is closed");
        state_->tasks.push_back(std::move(task));
    }
    state_->ready.notify_one();
}

void ThreadPool::close() {
    {
        std::lock_guard lock(state_->mutex);
        state_->closed = true;
    }
    state_->ready.notify_all();
}

void ThreadPool::waitIdle() {
    for (const auto& worker : state_->workers)
        if (worker.get_id() == std::this_thread::get_id())
            throw std::logic_error("a worker cannot wait for its own pool to become idle");
    std::unique_lock lock(state_->mutex);
    state_->idle.wait(lock, [&] { return state_->tasks.empty() && !state_->active; });
}

} // namespace xolver::parallel
