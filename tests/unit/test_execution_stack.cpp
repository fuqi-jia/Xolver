#include <doctest/doctest.h>
#include "base/ExecutionStack.h"
#include <algorithm>
#include <stdexcept>

#ifdef __linux__
#include <pthread.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

namespace {
constexpr std::size_t stackBytes = 512UL * 1024 * 1024;

bool currentStackAtLeast(std::size_t bytes) {
    if (syscall(SYS_gettid) == getpid()) {
        rlimit limit;
        return getrlimit(RLIMIT_STACK, &limit) == 0 &&
            (limit.rlim_cur == RLIM_INFINITY || limit.rlim_cur >= bytes);
    }
    pthread_attr_t attributes;
    if (pthread_getattr_np(pthread_self(), &attributes) != 0) return false;
    std::size_t size = 0;
    const bool enough = pthread_attr_getstacksize(&attributes, &size) == 0 && size >= bytes;
    pthread_attr_destroy(&attributes);
    return enough;
}
} // namespace

TEST_CASE("Execution stack: provision the main thread and restore its soft limit") {
    rlimit previous;
    REQUIRE(getrlimit(RLIMIT_STACK, &previous) == 0);
    const auto caller = syscall(SYS_gettid);
    bool ran = false, enough = false;
    long executor = 0;
    xolver::withExecutionStack([&] {
        ran = true;
        executor = syscall(SYS_gettid);
        enough = currentStackAtLeast(stackBytes);
    }, stackBytes);
    CHECK(ran);
    CHECK(enough);
    if (previous.rlim_max == RLIM_INFINITY || previous.rlim_max >= stackBytes)
        CHECK(executor == caller);
    rlimit restored;
    REQUIRE(getrlimit(RLIMIT_STACK, &restored) == 0);
    CHECK(restored.rlim_cur == previous.rlim_cur);
    CHECK(restored.rlim_max == previous.rlim_max);
}

TEST_CASE("Execution stack: exceptions restore the main soft limit") {
    rlimit previous;
    REQUIRE(getrlimit(RLIMIT_STACK, &previous) == 0);
    CHECK_THROWS_AS(xolver::withExecutionStack([] { throw std::runtime_error("stack action"); }),
                    std::runtime_error);
    rlimit restored;
    REQUIRE(getrlimit(RLIMIT_STACK, &restored) == 0);
    CHECK(restored.rlim_cur == previous.rlim_cur);
    CHECK(restored.rlim_max == previous.rlim_max);
}

TEST_CASE("Execution stack: a hard main-stack cap retains the large worker and its exception") {
    const auto child = fork();
    REQUIRE(child >= 0);
    if (child == 0) {
        // Lowering the hard limit is irreversible without privilege. Isolate
        // that condition so the test process retains its original resources.
        rlimit original;
        if (getrlimit(RLIMIT_STACK, &original) != 0) _exit(1);
        const auto cap = original.rlim_max == RLIM_INFINITY ? rlim_t(8UL * 1024 * 1024)
            : std::min(original.rlim_max, rlim_t(8UL * 1024 * 1024));
        const rlimit capped{cap, cap};
        if (setrlimit(RLIMIT_STACK, &capped) != 0) _exit(1);
        bool worker = false, enough = false, propagated = false;
        try {
            xolver::withExecutionStack([&] {
                worker = syscall(SYS_gettid) != getpid();
                enough = currentStackAtLeast(stackBytes);
                throw std::runtime_error("worker action");
            }, stackBytes);
        } catch (const std::runtime_error&) {
            propagated = true;
        } catch (...) {
            _exit(2);
        }
        rlimit restored;
        const bool unchanged = getrlimit(RLIMIT_STACK, &restored) == 0 &&
            restored.rlim_cur == capped.rlim_cur && restored.rlim_max == capped.rlim_max;
        _exit(worker && enough && propagated && unchanged ? 0 : 3);
    }
    int status = 0;
    REQUIRE(waitpid(child, &status, 0) == child);
    REQUIRE(WIFEXITED(status));
    CHECK(WEXITSTATUS(status) == 0);
}
#else
TEST_CASE("Execution stack: execute actions and propagate exceptions") {
    bool ran = false;
    xolver::withExecutionStack([&] { ran = true; });
    CHECK(ran);
    CHECK_THROWS_AS(xolver::withExecutionStack([] { throw std::runtime_error("action"); }),
                    std::runtime_error);
}
#endif
