#include "parallel/DeviceExecutor.h"
#include <exception>
#include <stdexcept>

#if XOLVER_WITH_CUDA
#include <cuda_runtime_api.h>
#endif
#if XOLVER_WITH_HIP
#include <hip/hip_runtime_api.h>
#endif
#if XOLVER_WITH_OPENACC
#include <openacc.h>
#endif

namespace xolver::parallel {
namespace {
#if XOLVER_WITH_CUDA
void cudaCheck(cudaError_t error) {
    if (error != cudaSuccess) throw std::runtime_error(cudaGetErrorString(error));
}
class CudaContext final : public DeviceContext {
    int device_;
    cudaStream_t stream_ = nullptr;
public:
    explicit CudaContext(int device) : device_(device) {}
    ~CudaContext() override {
        if (stream_) {
            int previous = 0;
            cudaGetDevice(&previous);
            cudaSetDevice(device_);
            cudaStreamDestroy(stream_);
            cudaSetDevice(previous);
        }
    }
    Backend backend() const noexcept override { return Backend::Cuda; }
    void activate() override {
        cudaCheck(cudaSetDevice(device_));
        if (!stream_) cudaCheck(cudaStreamCreateWithFlags(&stream_, cudaStreamNonBlocking));
    }
    void* allocate(std::size_t bytes) override {
        if (!bytes) return nullptr;
        void* result = nullptr;
        cudaCheck(cudaMalloc(&result, bytes));
        return result;
    }
    void release(void* pointer) noexcept override {
        if (pointer) { cudaStreamSynchronize(stream_); cudaFree(pointer); }
    }
    void upload(void* target, std::span<const std::uint8_t> source) override {
        if (!source.empty()) cudaCheck(cudaMemcpyAsync(target, source.data(), source.size(), cudaMemcpyHostToDevice, stream_));
    }
    void download(std::span<std::uint8_t> target, const void* source) override {
        if (!target.empty()) cudaCheck(cudaMemcpyAsync(target.data(), source, target.size(), cudaMemcpyDeviceToHost, stream_));
    }
    void fill(void* target, std::uint8_t value, std::size_t bytes) override {
        if (bytes) cudaCheck(cudaMemsetAsync(target, value, bytes, stream_));
    }
    void wait() override { cudaCheck(cudaStreamSynchronize(stream_)); }
    void* nativeStream() const noexcept override { return stream_; }
    std::string description() const override { return "CUDA device " + std::to_string(device_); }
};
#endif

#if XOLVER_WITH_HIP
void hipCheck(hipError_t error) {
    if (error != hipSuccess) throw std::runtime_error(hipGetErrorString(error));
}
class HipContext final : public DeviceContext {
    int device_;
    hipStream_t stream_ = nullptr;
public:
    explicit HipContext(int device) : device_(device) {}
    ~HipContext() override {
        if (stream_) {
            int previous = 0;
            hipGetDevice(&previous);
            hipSetDevice(device_);
            hipStreamDestroy(stream_);
            hipSetDevice(previous);
        }
    }
    Backend backend() const noexcept override { return Backend::Hip; }
    void activate() override {
        hipCheck(hipSetDevice(device_));
        if (!stream_) hipCheck(hipStreamCreateWithFlags(&stream_, hipStreamNonBlocking));
    }
    void* allocate(std::size_t bytes) override {
        if (!bytes) return nullptr;
        void* result = nullptr;
        hipCheck(hipMalloc(&result, bytes));
        return result;
    }
    void release(void* pointer) noexcept override {
        if (pointer) { hipStreamSynchronize(stream_); hipFree(pointer); }
    }
    void upload(void* target, std::span<const std::uint8_t> source) override {
        if (!source.empty()) hipCheck(hipMemcpyAsync(target, source.data(), source.size(), hipMemcpyHostToDevice, stream_));
    }
    void download(std::span<std::uint8_t> target, const void* source) override {
        if (!target.empty()) hipCheck(hipMemcpyAsync(target.data(), source, target.size(), hipMemcpyDeviceToHost, stream_));
    }
    void fill(void* target, std::uint8_t value, std::size_t bytes) override {
        if (bytes) hipCheck(hipMemsetAsync(target, value, bytes, stream_));
    }
    void wait() override { hipCheck(hipStreamSynchronize(stream_)); }
    void* nativeStream() const noexcept override { return stream_; }
    std::string description() const override { return "HIP device " + std::to_string(device_); }
};
#endif

#if XOLVER_WITH_OPENACC
class OpenAccContext final : public DeviceContext {
    int device_;
public:
    explicit OpenAccContext(int device) : device_(device) {}
    Backend backend() const noexcept override { return Backend::OpenAcc; }
    void activate() override {
        if (device_ >= acc_get_num_devices(acc_device_default))
            throw std::runtime_error("OpenACC device is unavailable");
        acc_set_device_num(device_, acc_device_default);
    }
    void* allocate(std::size_t bytes) override {
        if (!bytes) return nullptr;
        void* pointer = acc_malloc(bytes);
        if (!pointer) throw std::bad_alloc();
        return pointer;
    }
    void release(void* pointer) noexcept override {
        if (pointer) { acc_wait(queue()); acc_free(pointer); }
    }
    void upload(void* target, std::span<const std::uint8_t> source) override {
        if (!source.empty()) acc_memcpy_to_device(target, const_cast<std::uint8_t*>(source.data()), source.size());
    }
    void download(std::span<std::uint8_t> target, const void* source) override {
        wait();
        if (!target.empty()) acc_memcpy_from_device(target.data(), const_cast<void*>(source), target.size());
    }
    void fill(void* target, std::uint8_t value, std::size_t bytes) override {
        auto* data = static_cast<std::uint8_t*>(target);
        const int workQueue = queue();
#pragma acc parallel loop deviceptr(data) async(workQueue)
        for (std::size_t index = 0; index < bytes; ++index) data[index] = value;
    }
    void wait() override { acc_wait(queue()); }
    void* nativeStream() const noexcept override { return nullptr; }
    std::string description() const override {
        return acc_get_device_type() == acc_device_host ? "OpenACC host" : "OpenACC device";
    }
};
#endif
}

DeviceExecutor::DeviceExecutor(std::unique_ptr<DeviceContext> context) : context_(std::move(context)) {
    if (!context_) throw std::invalid_argument("device context is required");
}
DeviceExecutor::~DeviceExecutor() = default;

std::future<void> DeviceExecutor::submit(std::function<void(DeviceContext&)> task) {
    if (!task) throw std::invalid_argument("device task is required");
    return pool_.submit([this, task = std::move(task)] {
        context_->activate();
        try {
            task(*context_);
            context_->wait();
        } catch (...) {
            auto failure = std::current_exception();
            try { context_->wait(); } catch (...) {}
            std::rethrow_exception(failure);
        }
    });
}

std::unique_ptr<DeviceExecutor> makeDeviceExecutor(Backend backend, int device) {
    if (device < 0) throw std::invalid_argument("device index must be nonnegative");
    switch (backend) {
#if XOLVER_WITH_CUDA
        case Backend::Cuda: return std::make_unique<DeviceExecutor>(std::make_unique<CudaContext>(device));
#endif
#if XOLVER_WITH_HIP
        case Backend::Hip: return std::make_unique<DeviceExecutor>(std::make_unique<HipContext>(device));
#endif
#if XOLVER_WITH_OPENACC
        case Backend::OpenAcc: return std::make_unique<DeviceExecutor>(std::make_unique<OpenAccContext>(device));
#endif
        default: throw std::invalid_argument("device backend was not enabled at build time");
    }
}

} // namespace xolver::parallel
