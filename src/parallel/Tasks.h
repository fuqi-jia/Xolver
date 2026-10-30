#pragma once

#include "parallel/ThreadPool.h"
#include <cstdint>
#include <functional>
#include <iosfwd>
#include <memory>
#include <shared_mutex>
#include <span>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace xolver::parallel {

using Bytes = std::vector<std::uint8_t>;
struct Task {
    std::string id;
    std::string handler;
    Bytes payload;
};
struct TaskResult {
    std::string id;
    bool success = true;
    Bytes payload;
    std::string error;
};

// Handlers are installed on every worker. Only names and bytes cross process
// boundaries; captured C++ state and device addresses remain worker-local.
class TaskRegistry {
public:
    using Handler = std::function<Bytes(std::span<const std::uint8_t>)>;
    void add(std::string name, Handler handler);
    TaskResult execute(const Task&) const;
private:
    mutable std::shared_mutex mutex_;
    std::unordered_map<std::string, Handler> handlers_;
};

class BatchExecutor {
public:
    virtual ~BatchExecutor() = default;
    virtual std::size_t concurrency() const noexcept = 0;
    virtual std::vector<TaskResult> run(const std::vector<Task>&) = 0;
};

class LocalTaskExecutor final : public BatchExecutor {
    std::shared_ptr<const TaskRegistry> registry_;
    ThreadPool pool_;
public:
    explicit LocalTaskExecutor(std::shared_ptr<const TaskRegistry>, std::size_t workers = 1);
    std::size_t concurrency() const noexcept override { return pool_.concurrency(); }
    std::vector<TaskResult> run(const std::vector<Task>&) override;
};

// Versioned, language-neutral JSON wire format. Byte arrays retain arbitrary
// binary input. Decoders reject malformed messages rather than truncating bytes.
std::string encodeTasks(const std::vector<Task>&);
std::vector<Task> decodeTasks(std::string_view, std::size_t maxBytes = 64 * 1024 * 1024);
std::string encodeResults(const std::vector<TaskResult>&);
std::vector<TaskResult> decodeResults(std::string_view, std::size_t maxBytes = 64 * 1024 * 1024);

// Persistent stream transport: an unsigned 64-bit big-endian length followed
// by one nonempty message. EOF is valid only between frames. No solver state
// is implied by keeping the transport open.
bool readFrame(std::istream&, std::string&, std::size_t maxBytes = 64 * 1024 * 1024);
void writeFrame(std::ostream&, std::string_view, std::size_t maxBytes = 64 * 1024 * 1024);

enum class Backend { Local, Mpi, Spark, Dask, Cuda, Hip, OpenAcc };
bool compiled(Backend) noexcept;
std::vector<std::string> compiledBackends();

} // namespace xolver::parallel
