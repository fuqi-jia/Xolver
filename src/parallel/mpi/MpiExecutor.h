#pragma once

#include "parallel/Tasks.h"

#if defined(XOLVER_WITH_MPI) && XOLVER_WITH_MPI
#include <mpi.h>
#include <thread>

namespace xolver::parallel {

// Collective batch API: all communicator ranks call run(), on the thread
// which constructed the executor, with the same root. Only root supplies work
// and receives the ordered results. Initialize MPI before construction and
// destroy executors before MPI_Finalize. OpenMPI and MPICH use this same API.
class MpiExecutor final : public BatchExecutor {
    std::shared_ptr<const TaskRegistry> registry_;
    MPI_Comm communicator_ = MPI_COMM_NULL;
    int rank_ = 0, ranks_ = 1, root_ = 0;
    std::size_t maxWireBytes_;
    std::thread::id owner_;
public:
    explicit MpiExecutor(std::shared_ptr<const TaskRegistry>, MPI_Comm = MPI_COMM_WORLD,
                         int root = 0, std::size_t maxWireBytes = 64 * 1024 * 1024);
    ~MpiExecutor() override;
    MpiExecutor(const MpiExecutor&) = delete;
    MpiExecutor& operator=(const MpiExecutor&) = delete;
    std::size_t concurrency() const noexcept override { return static_cast<std::size_t>(ranks_); }
    std::vector<TaskResult> run(const std::vector<Task>&) override;
    int rank() const noexcept { return rank_; }
    int root() const noexcept { return root_; }
};

} // namespace xolver::parallel
#endif
