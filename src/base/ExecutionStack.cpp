#include "base/ExecutionStack.h"

#include <exception>

#if defined(__unix__) || defined(__APPLE__)
#include <pthread.h>
#endif
#ifdef __linux__
#include <sys/resource.h>
#include <sys/syscall.h>
#include <unistd.h>
#endif

namespace xolver {
namespace {

#if defined(__unix__) || defined(__APPLE__)
struct StackAction {
    const std::function<void()>& action;
    std::exception_ptr exception;
};

void* executeStackAction(void* pointer) noexcept {
    auto& context = *static_cast<StackAction*>(pointer);
    try {
        context.action();
    } catch (...) {
        context.exception = std::current_exception();
    }
    return nullptr;
}
#endif

#ifdef __linux__
struct RestoreStackLimit {
    rlimit previous;
    ~RestoreStackLimit() { setrlimit(RLIMIT_STACK, &previous); }
};
#endif

} // namespace

void withExecutionStack(const std::function<void()>& action, std::size_t minimumBytes) {
#ifdef __linux__
    // RLIMIT_STACK controls growth of the main stack. Avoid creating a thread
    // merely to reserve stack space: even a joined worker makes libc use its
    // multithreaded allocation paths during allocation-heavy exact arithmetic.
    rlimit previous;
    if (syscall(SYS_gettid) == getpid() && getrlimit(RLIMIT_STACK, &previous) == 0) {
        if (previous.rlim_cur == RLIM_INFINITY || previous.rlim_cur >= minimumBytes) {
            action();
            return;
        }
        if (minimumBytes < static_cast<std::size_t>(RLIM_INFINITY) &&
            (previous.rlim_max == RLIM_INFINITY || previous.rlim_max >= minimumBytes)) {
            auto enlarged = previous;
            enlarged.rlim_cur = static_cast<rlim_t>(minimumBytes);
            if (setrlimit(RLIMIT_STACK, &enlarged) == 0) {
                RestoreStackLimit restore{previous};
                action();
                return;
            }
        }
    }
#endif

#if defined(__unix__) || defined(__APPLE__)
    pthread_attr_t attributes;
    if (pthread_attr_init(&attributes) == 0) {
        StackAction context{action, {}};
        pthread_t thread;
        const bool started = pthread_attr_setstacksize(&attributes, minimumBytes) == 0 &&
            pthread_create(&thread, &attributes, executeStackAction, &context) == 0;
        pthread_attr_destroy(&attributes);
        if (started) {
            // The joinable worker borrows this stack context. A failed join
            // cannot safely return while that worker may still access it.
            if (pthread_join(thread, nullptr) != 0) std::terminate();
            if (context.exception) std::rethrow_exception(context.exception);
            return;
        }
    }
#endif
    action();
}

} // namespace xolver
