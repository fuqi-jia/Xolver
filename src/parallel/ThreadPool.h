#pragma once

#include "parallel/Executor.h"

namespace xolver::parallel {

class ThreadPool final : public Executor {
    struct State;
    std::unique_ptr<State> state_;
    void enqueue(Task task) override;

public:
    // Explicit width avoids silently oversubscribing a caller's CPU lease.
    explicit ThreadPool(std::size_t workers = 1);
    ~ThreadPool() override;
    ThreadPool(const ThreadPool&) = delete;
    ThreadPool& operator=(const ThreadPool&) = delete;

    std::size_t concurrency() const noexcept override;
    // Stop accepting work; accepted tasks still drain. Idempotent/nonblocking.
    void close();
    // Wait for the queue and active tasks to empty. Call from outside the pool.
    void waitIdle();
};

} // namespace xolver::parallel
