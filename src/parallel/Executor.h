#pragma once

#include <cstddef>
#include <functional>
#include <future>
#include <memory>
#include <tuple>
#include <type_traits>
#include <utility>

namespace xolver::parallel {

// Scheduling is independent of solver state, theory and result type. An
// implementation must invoke every accepted task exactly once.
class Executor {
protected:
    using Task = std::function<void()>;
    virtual void enqueue(Task task) = 0;

public:
    virtual ~Executor() = default;
    virtual std::size_t concurrency() const noexcept = 0;

    // Arguments are copied/moved as with std::async; use std::ref explicitly
    // for references. User exceptions are delivered through the future.
    template<class Function, class... Args>
    auto submit(Function&& function, Args&&... args)
        -> std::future<std::invoke_result_t<std::decay_t<Function>, std::decay_t<Args>...>> {
        using Result = std::invoke_result_t<std::decay_t<Function>, std::decay_t<Args>...>;
        auto call = [function = std::forward<Function>(function),
                     values = std::make_tuple(std::forward<Args>(args)...)]() mutable -> Result {
            return std::apply(std::move(function), std::move(values));
        };
        auto task = std::make_shared<std::packaged_task<Result()>>(std::move(call));
        auto result = task->get_future();
        enqueue([task] { (*task)(); });
        return result;
    }
};

} // namespace xolver::parallel
