#include "parallel/Tasks.h"
#include "xolver/Solver.h"
#include <nlohmann/json.hpp>
#include <atomic>
#include <chrono>
#include <cstdio>
#include <filesystem>
#include <iostream>
#include <sstream>
#include <stdexcept>

namespace {
using namespace xolver::parallel;
using Json = nlohmann::json;

class InputFile {
    std::filesystem::path path_;
public:
    explicit InputFile(const std::string& text) {
        static std::atomic<unsigned long long> serial{0};
        const auto stamp = std::chrono::steady_clock::now().time_since_epoch().count();
        for (int attempt = 0; attempt < 32; ++attempt) {
            path_ = std::filesystem::temp_directory_path() /
                ("xolver-task-" + std::to_string(stamp) + "-" + std::to_string(serial++) + ".smt2");
            auto* file = std::fopen(path_.string().c_str(), "wbx");
            if (!file) continue;
            const bool written = std::fwrite(text.data(), 1, text.size(), file) == text.size();
            const bool closed = std::fclose(file) == 0;
            if (written && closed) return;
            std::error_code ignored;
            std::filesystem::remove(path_, ignored);
            throw std::runtime_error("cannot write worker input");
        }
        throw std::runtime_error("cannot create exclusive worker input file");
    }
    ~InputFile() {
        std::error_code ignored;
        std::filesystem::remove(path_, ignored);
    }
    std::string path() const { return path_.string(); }
};

Bytes solve(std::span<const std::uint8_t> payload) {
    const auto request = Json::parse(payload.begin(), payload.end());
    const auto source = request.at("smt2").get<std::string>();
    if (request.contains("timeout_ms") && !request.at("timeout_ms").is_number_integer())
        throw std::invalid_argument("timeout_ms must be a nonnegative integer");
    const auto milliseconds = request.value("timeout_ms", std::int64_t(60000));
    if (milliseconds < 0) throw std::invalid_argument("timeout_ms must be nonnegative");
    InputFile input(source);
    xolver::Solver solver;
    solver.setRuntimeParameter("XOLVER_WALLCLOCK_MS", std::to_string(milliseconds));
    if (!solver.parseFile(input.path())) throw std::invalid_argument("invalid SMT-LIB input");
    const auto result = solver.checkSat();
    Json response{{"result", xolver::toString(result)}};
    if (result == xolver::Result::Unknown) response["reason"] = solver.lastUnknownReason();
    if (result == xolver::Result::Sat && request.value("model", false)) {
        const auto checked = solver.validateModel();
        if (checked == xolver::Solver::ModelValidation::Violated)
            throw std::runtime_error("solver model violates the original input");
        response["model_validation"] = checked == xolver::Solver::ModelValidation::Satisfied
            ? "satisfied" : "indeterminate";
        std::ostringstream model;
        solver.dumpModel(model);
        response["model"] = model.str();
    }
    const auto text = response.dump();
    return Bytes(text.begin(), text.end());
}
}

int main() {
    try {
        constexpr std::size_t maximum = 64 * 1024 * 1024;
        TaskRegistry registry;
        registry.add("echo", [](auto payload) { return Bytes(payload.begin(), payload.end()); });
        registry.add("smt.solve", solve);
        registry.add("backends", [](auto) {
            const auto text = Json(compiledBackends()).dump();
            return Bytes(text.begin(), text.end());
        });
        // Library diagnostics belong on stderr; stdout is exclusively the wire
        // protocol. The worker executes snapshots sequentially in this process.
        std::ostream output(std::cout.rdbuf());
        std::cout.rdbuf(std::cerr.rdbuf());
        std::string input;
        while (readFrame(std::cin, input, maximum)) {
            const auto tasks = decodeTasks(input, maximum);
            std::vector<TaskResult> results;
            for (const auto& task : tasks) results.push_back(registry.execute(task));
            writeFrame(output, encodeResults(results), maximum);
        }
        return 0;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 2;
    }
}
