#include "parallel/DeviceExecutor.h"
#include "parallel/mpi/MpiExecutor.h"
#include <algorithm>
#include <iostream>
#include <stdexcept>

namespace {
using namespace xolver::parallel;
Backend deviceBackend(const std::string& name) {
    if (name == "cuda") return Backend::Cuda;
    if (name == "hip") return Backend::Hip;
    if (name == "openacc") return Backend::OpenAcc;
    throw std::invalid_argument("device must be cuda, hip or openacc");
}
std::shared_ptr<TaskRegistry> registry(std::shared_ptr<DeviceExecutor> device = {}) {
    auto result = std::make_shared<TaskRegistry>();
    result->add("echo", [](auto input) { return Bytes(input.begin(), input.end()); });
    result->add("fail", [](auto) -> Bytes { throw std::runtime_error("expected task failure"); });
    result->add("fill", [device](auto input) {
        Bytes output(input.size(), 42);
        if (device) device->submit([&](DeviceContext& context) {
            DeviceBuffer buffer(context, input.size());
            context.upload(buffer.data(), input);
            context.fill(buffer.data(), 42, input.size());
            context.download(output, buffer.data());
        }).get();
        return output;
    });
    return result;
}
void verify(const std::vector<TaskResult>& result) {
    if (result.size() != 3 || !result[0].success || result[0].payload != Bytes({0, 128, 255}) ||
        result[1].success || !result[2].success || result[2].payload != Bytes(32, 42))
        throw std::runtime_error("task result validation failed");
}
const std::vector<Task> tasks = {{"echo", "echo", {0, 128, 255}}, {"error", "fail", {}},
                                  {"fill", "fill", Bytes(32, 1)}};
}

int main(int argc, char** argv) {
    try {
        const std::string mode = argc > 1 ? argv[1] : "local";
        if (mode == "local") {
            LocalTaskExecutor executor(registry(), 2);
            verify(executor.run(tasks));
            std::cout << "local: binary payloads, ordered results and errors passed\n";
        } else if (mode == "mpi") {
#if defined(XOLVER_WITH_MPI) && XOLVER_WITH_MPI
            int provided = 0;
            MPI_Init_thread(&argc, &argv, MPI_THREAD_FUNNELED, &provided);
            if (provided < MPI_THREAD_FUNNELED) throw std::runtime_error("MPI lacks FUNNELED thread support");
            {
                int ranks = 0;
                MPI_Comm_size(MPI_COMM_WORLD, &ranks);
                std::shared_ptr<DeviceExecutor> device;
                if (argc > 2) device = makeDeviceExecutor(deviceBackend(argv[2]));
                MpiExecutor executor(registry(device), MPI_COMM_WORLD, ranks > 1 ? 1 : 0);
                const auto result = executor.run(executor.rank() == executor.root() ? tasks : std::vector<Task>{});
                if (executor.rank() == executor.root()) verify(result);
                if (!executor.run({}).empty()) throw std::runtime_error("empty MPI batch returned work");
                if (executor.rank() == executor.root())
                    std::cout << "mpi: " << ranks << " ranks, nonzero root and ordered results passed\n";
            }
            MPI_Finalize();
#else
            throw std::runtime_error("MPI was not enabled at build time");
#endif
        } else {
            auto device = makeDeviceExecutor(deviceBackend(mode));
            Bytes input{0, 1, 127, 255}, output(input.size());
            std::string description;
            device->submit([&](DeviceContext& context) {
                DeviceBuffer buffer(context, input.size());
                context.upload(buffer.data(), input);
                context.download(output, buffer.data());
                context.wait();
                if (output != input) throw std::runtime_error("device round-trip failed");
                context.fill(buffer.data(), 42, input.size());
                context.download(output, buffer.data());
                description = context.description();
            }).get();
            if (output != Bytes(input.size(), 42)) throw std::runtime_error("device fill failed");
            std::cout << description << ": upload, fill and download passed\n";
        }
        return 0;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
