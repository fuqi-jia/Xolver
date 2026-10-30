#include "parallel/Tasks.h"
#include "parallel/DeviceExecutor.h"
#include <doctest/doctest.h>
#include <algorithm>
#include <atomic>
#include <stdexcept>
#include <sstream>

using namespace xolver::parallel;

TEST_CASE("parallel tasks: binary transport, ordered results and isolated errors") {
    auto registry = std::make_shared<TaskRegistry>();
    registry->add("echo", [](std::span<const std::uint8_t> data) { return Bytes(data.begin(), data.end()); });
    registry->add("fail", [](auto) -> Bytes { throw std::runtime_error("handler failed"); });
    CHECK_THROWS_AS(registry->add("echo", [](auto) { return Bytes{}; }), std::invalid_argument);
    const std::vector<Task> input{{"a", "echo", {0, 255, 128}}, {"b", "fail", {}}, {"c", "absent", {}}};
    const auto decoded = decodeTasks(encodeTasks(input));
    REQUIRE(decoded.size() == 3);
    CHECK(decoded[0].payload == input[0].payload);
    LocalTaskExecutor executor(registry, 3);
    const auto results = decodeResults(encodeResults(executor.run(decoded)));
    REQUIRE(results.size() == 3);
    CHECK(results[0].id == "a");
    CHECK(results[0].success);
    CHECK(results[0].payload == input[0].payload);
    CHECK_FALSE(results[1].success);
    CHECK(results[1].error == "handler failed");
    CHECK_FALSE(results[2].success);
    CHECK(executor.run({}).empty());
    CHECK(compiled(Backend::Local));
}

TEST_CASE("parallel tasks: protocol rejects truncation, wrong versions and wire overruns") {
    for (const char* payload : {"[-1]", "[256]", "[1.5]", "[true]", "null"}) {
        const std::string input = std::string("{\"version\":1,\"tasks\":[{\"id\":\"a\",\"handler\":\"echo\",\"payload\":") + payload + "}]}";
        CHECK_THROWS(decodeTasks(input));
    }
    CHECK_THROWS(decodeTasks("{\"version\":1.0,\"tasks\":[]}"));
    CHECK_THROWS(decodeTasks("{\"version\":true,\"tasks\":[]}"));
    CHECK_THROWS(decodeTasks(encodeTasks({}), 1));
    CHECK_THROWS(decodeResults("{\"version\":1,\"results\":[{}]}"));
}

TEST_CASE("parallel tasks: persistent frames preserve binary boundaries and clean EOF") {
    std::stringstream stream;
    const std::string binary("\0\xff\n", 3);
    writeFrame(stream, binary);
    writeFrame(stream, "second");
    std::string output;
    REQUIRE(readFrame(stream, output));
    CHECK(output == binary);
    REQUIRE(readFrame(stream, output));
    CHECK(output == "second");
    CHECK_FALSE(readFrame(stream, output));
    CHECK(output.empty());
}

TEST_CASE("parallel tasks: framed input rejects truncation and lengths before allocation") {
    std::stringstream complete;
    writeFrame(complete, "payload");
    const auto wire = complete.str();
    std::string output;
    for (std::size_t length = 1; length < wire.size(); ++length) {
        std::istringstream partial(wire.substr(0, length));
        CHECK_THROWS(readFrame(partial, output));
    }
    for (const auto& invalid : {std::string(8, '\0'), std::string(8, '\xff')}) {
        std::istringstream stream(invalid);
        CHECK_THROWS_AS(readFrame(stream, output), std::length_error);
    }
    std::istringstream limited(wire);
    CHECK_THROWS_AS(readFrame(limited, output, 6), std::length_error);
    CHECK_THROWS_AS(writeFrame(complete, "", 6), std::length_error);
    CHECK_THROWS_AS(writeFrame(complete, "payload", 6), std::length_error);
}

namespace {
class HostContext final : public DeviceContext {
    std::atomic<int>& completed_;
public:
    explicit HostContext(std::atomic<int>& completed) : completed_(completed) {}
    Backend backend() const noexcept override { return Backend::Local; }
    void activate() override {}
    void* allocate(std::size_t n) override { return new std::uint8_t[n]; }
    void release(void* p) noexcept override { delete[] static_cast<std::uint8_t*>(p); }
    void upload(void* p, std::span<const std::uint8_t> data) override {
        std::copy(data.begin(), data.end(), static_cast<std::uint8_t*>(p));
    }
    void download(std::span<std::uint8_t> data, const void* p) override {
        std::copy_n(static_cast<const std::uint8_t*>(p), data.size(), data.begin());
    }
    void fill(void* p, std::uint8_t byte, std::size_t n) override {
        std::fill_n(static_cast<std::uint8_t*>(p), n, byte);
    }
    void wait() override { ++completed_; }
    void* nativeStream() const noexcept override { return nullptr; }
    std::string description() const override { return "unit-test host context"; }
};
}

TEST_CASE("parallel devices: injected contexts preserve lifetimes and future exceptions") {
    std::atomic<int> completed{0};
    std::future<void> pending;
    {
        DeviceExecutor executor(std::make_unique<HostContext>(completed));
        auto failure = executor.submit([](DeviceContext&) { throw std::runtime_error("device task failed"); });
        CHECK_THROWS_AS(failure.get(), std::runtime_error);
        pending = executor.submit([](DeviceContext& context) {
            DeviceBuffer buffer(context, 4);
            context.fill(buffer.data(), 7, 4);
            Bytes host(4);
            context.download(host, buffer.data());
            if (host != Bytes(4, 7)) throw std::runtime_error("copy failed");
        });
    }
    CHECK_NOTHROW(pending.get());
    CHECK(completed >= 2);
    for (Backend backend : {Backend::Cuda, Backend::Hip, Backend::OpenAcc})
        if (!compiled(backend)) CHECK_THROWS_AS(makeDeviceExecutor(backend), std::invalid_argument);
}
