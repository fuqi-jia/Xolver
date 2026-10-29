#include "parallel/Tasks.h"
#include <nlohmann/json.hpp>
#include <mutex>
#include <stdexcept>

namespace xolver::parallel {
namespace {
using Json = nlohmann::json;

Bytes bytes(const Json& value) {
    if (!value.is_array()) throw std::invalid_argument("payload must be a byte array");
    Bytes result;
    result.reserve(value.size());
    for (const auto& item : value) {
        if (!item.is_number_integer() || item < 0 || item > 255)
            throw std::invalid_argument("payload byte is outside [0,255]");
        result.push_back(item.get<std::uint8_t>());
    }
    return result;
}
Json message(std::string_view input, std::size_t maximum, const char* field) {
    if (input.size() > maximum) throw std::length_error("task message exceeds wire budget");
    auto parsed = Json::parse(input);
    if (!parsed.is_object() || !parsed.at("version").is_number_integer() || parsed.at("version") != 1 || !parsed.at(field).is_array())
        throw std::invalid_argument("invalid task protocol message");
    return parsed;
}
std::string dump(const Json& value) {
    return value.dump(-1, ' ', false, Json::error_handler_t::replace);
}
}

void TaskRegistry::add(std::string name, Handler handler) {
    if (name.empty() || !handler) throw std::invalid_argument("task name and handler are required");
    std::unique_lock lock(mutex_);
    if (!handlers_.emplace(std::move(name), std::move(handler)).second)
        throw std::invalid_argument("task handler is already registered");
}

TaskResult TaskRegistry::execute(const Task& task) const {
    TaskResult result;
    result.id = task.id;
    try {
        Handler handler;
        {
            std::shared_lock lock(mutex_);
            const auto found = handlers_.find(task.handler);
            if (found == handlers_.end()) throw std::invalid_argument("unknown task handler: " + task.handler);
            handler = found->second;
        }
        result.payload = handler(task.payload);
    } catch (const std::exception& error) {
        result.success = false;
        result.error = error.what();
    } catch (...) {
        result.success = false;
        result.error = "task handler threw a non-standard exception";
    }
    return result;
}

LocalTaskExecutor::LocalTaskExecutor(std::shared_ptr<const TaskRegistry> registry, std::size_t workers)
    : registry_(std::move(registry)), pool_(workers) {
    if (!registry_) throw std::invalid_argument("task registry is required");
}

std::vector<TaskResult> LocalTaskExecutor::run(const std::vector<Task>& tasks) {
    std::vector<std::future<TaskResult>> pending;
    for (const auto& task : tasks)
        pending.push_back(pool_.submit([registry = registry_, task] { return registry->execute(task); }));
    std::vector<TaskResult> results;
    for (auto& result : pending) results.push_back(result.get());
    return results;
}

std::string encodeTasks(const std::vector<Task>& tasks) {
    Json values = Json::array();
    for (const auto& task : tasks)
        values.push_back({{"id", task.id}, {"handler", task.handler}, {"payload", task.payload}});
    return dump({{"version", 1}, {"tasks", std::move(values)}});
}
std::vector<Task> decodeTasks(std::string_view input, std::size_t maximum) {
    const auto parsed = message(input, maximum, "tasks");
    std::vector<Task> tasks;
    for (const auto& task : parsed.at("tasks"))
        tasks.push_back({task.at("id").get<std::string>(), task.at("handler").get<std::string>(),
                         bytes(task.at("payload"))});
    return tasks;
}
std::string encodeResults(const std::vector<TaskResult>& results) {
    Json values = Json::array();
    for (const auto& result : results)
        values.push_back({{"id", result.id}, {"ok", result.success}, {"payload", result.payload},
                          {"error", result.error}});
    return dump({{"version", 1}, {"results", std::move(values)}});
}
std::vector<TaskResult> decodeResults(std::string_view input, std::size_t maximum) {
    const auto parsed = message(input, maximum, "results");
    std::vector<TaskResult> results;
    for (const auto& result : parsed.at("results"))
        results.push_back({result.at("id").get<std::string>(), result.at("ok").get<bool>(),
                           bytes(result.at("payload")), result.at("error").get<std::string>()});
    return results;
}

bool compiled(Backend backend) noexcept {
    switch (backend) {
        case Backend::Local: return true;
        case Backend::Mpi: return XOLVER_WITH_MPI;
        case Backend::Spark: return XOLVER_WITH_SPARK;
        case Backend::Dask: return XOLVER_WITH_DASK;
        case Backend::Cuda: return XOLVER_WITH_CUDA;
        case Backend::Hip: return XOLVER_WITH_HIP;
        case Backend::OpenAcc: return XOLVER_WITH_OPENACC;
    }
    return false;
}
std::vector<std::string> compiledBackends() {
    std::vector<std::string> names;
    for (const auto& [backend, name] : {std::pair{Backend::Local, "local"}, {Backend::Mpi, "mpi"},
         {Backend::Spark, "spark"}, {Backend::Dask, "dask"}, {Backend::Cuda, "cuda"},
         {Backend::Hip, "hip"}, {Backend::OpenAcc, "openacc"}})
        if (compiled(backend)) names.emplace_back(name);
    return names;
}

} // namespace xolver::parallel
