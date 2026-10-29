#pragma once

#include "parallel/Tasks.h"
#include <cstddef>
#include <future>
#include <memory>

namespace xolver::parallel {

// Device operations run inside submit(). A kernel-owning client may use the
// CUDA/HIP native stream or OpenACC queue; pointers never cross worker nodes.
class DeviceContext {
public:
    virtual ~DeviceContext() = default;
    virtual Backend backend() const noexcept = 0;
    virtual void activate() = 0;
    virtual void* allocate(std::size_t bytes) = 0;
    virtual void release(void*) noexcept = 0;
    virtual void upload(void* device, std::span<const std::uint8_t> host) = 0;
    virtual void download(std::span<std::uint8_t> host, const void* device) = 0;
    virtual void fill(void* device, std::uint8_t value, std::size_t bytes) = 0;
    virtual void wait() = 0;
    virtual void* nativeStream() const noexcept = 0;
    virtual int queue() const noexcept { return 0; }
    virtual std::string description() const = 0;
};

class DeviceBuffer {
    DeviceContext& context_;
    void* data_;
public:
    DeviceBuffer(DeviceContext& context, std::size_t bytes)
        : context_(context), data_(context.allocate(bytes)) {}
    ~DeviceBuffer() { context_.release(data_); }
    DeviceBuffer(const DeviceBuffer&) = delete;
    DeviceBuffer& operator=(const DeviceBuffer&) = delete;
    void* data() const noexcept { return data_; }
};

class DeviceExecutor {
    // The pool drains before context destruction.
    std::unique_ptr<DeviceContext> context_;
    ThreadPool pool_{1};
public:
    explicit DeviceExecutor(std::unique_ptr<DeviceContext>);
    ~DeviceExecutor();
    std::future<void> submit(std::function<void(DeviceContext&)>);
    void close() { pool_.close(); }
};

// Rejects backends disabled at configure time. Device initialization and
// hardware errors reach the submitted future. OpenACC may select a host device;
// description() reports that explicitly.
std::unique_ptr<DeviceExecutor> makeDeviceExecutor(Backend, int device = 0);

} // namespace xolver::parallel
