#include "parallel/mpi/MpiExecutor.h"

#if defined(XOLVER_WITH_MPI) && XOLVER_WITH_MPI
#include <limits>
#include <stdexcept>

namespace xolver::parallel {
namespace {
void checked(int code) {
    if (code == MPI_SUCCESS) return;
    char buffer[MPI_MAX_ERROR_STRING];
    int length = 0;
    MPI_Error_string(code, buffer, &length);
    throw std::runtime_error(std::string("MPI: ") + std::string(buffer, length));
}
void broadcast(std::string& text, int root, int rank, MPI_Comm communicator) {
    int length = rank == root ? static_cast<int>(text.size()) : 0;
    checked(MPI_Bcast(&length, 1, MPI_INT, root, communicator));
    if (rank != root) text.resize(static_cast<std::size_t>(length));
    checked(MPI_Bcast(text.data(), length, MPI_CHAR, root, communicator));
}
}

MpiExecutor::MpiExecutor(std::shared_ptr<const TaskRegistry> registry, MPI_Comm communicator,
                         int root, std::size_t maximum)
    : registry_(std::move(registry)), root_(root), maxWireBytes_(maximum),
      owner_(std::this_thread::get_id()) {
    int initialized = 0, finalized = 0;
    MPI_Initialized(&initialized);
    if (initialized) MPI_Finalized(&finalized);
    if (!initialized || finalized) throw std::logic_error("MPI must be initialized and active");
    if (!registry_ || communicator == MPI_COMM_NULL || !maximum ||
        maximum > static_cast<std::size_t>(std::numeric_limits<int>::max()))
        throw std::invalid_argument("invalid MPI executor configuration");
    checked(MPI_Comm_size(communicator, &ranks_));
    if (root < 0 || root >= ranks_) throw std::invalid_argument("MPI root is outside the communicator");
    checked(MPI_Comm_dup(communicator, &communicator_));
    checked(MPI_Comm_set_errhandler(communicator_, MPI_ERRORS_RETURN));
    checked(MPI_Comm_rank(communicator_, &rank_));
}

MpiExecutor::~MpiExecutor() {
    int finalized = 0;
    MPI_Finalized(&finalized);
    if (!finalized && communicator_ != MPI_COMM_NULL) MPI_Comm_free(&communicator_);
}

std::vector<TaskResult> MpiExecutor::run(const std::vector<Task>& input) {
    if (std::this_thread::get_id() != owner_)
        throw std::logic_error("MPI executor must run on its owner thread");
    std::string request, error;
    if (rank_ == root_) {
        try {
            request = encodeTasks(input);
            if (request.size() > maxWireBytes_) throw std::length_error("MPI request exceeds wire budget");
        } catch (const std::exception& problem) {
            error = problem.what();
        }
    }
    // Root-side validation fails collectively, before other ranks await work.
    broadcast(error, root_, rank_, communicator_);
    if (!error.empty()) throw std::runtime_error(error);
    broadcast(request, root_, rank_, communicator_);
    const auto tasks = decodeTasks(request, maxWireBytes_);
    std::vector<TaskResult> local;
    for (std::size_t index = static_cast<std::size_t>(rank_); index < tasks.size();
         index += static_cast<std::size_t>(ranks_))
        local.push_back(registry_->execute(tasks[index]));

    std::string encoded;
    int failed = 0;
    try {
        encoded = encodeResults(local);
        failed = encoded.size() > maxWireBytes_;
    } catch (...) { failed = 1; }
    int anyFailed = 0;
    checked(MPI_Allreduce(&failed, &anyFailed, 1, MPI_INT, MPI_MAX, communicator_));
    if (anyFailed) throw std::length_error("MPI worker output exceeds wire budget or cannot be encoded");
    int length = static_cast<int>(encoded.size());
    std::vector<int> lengths(static_cast<std::size_t>(ranks_)), offsets(lengths.size());
    checked(MPI_Gather(&length, 1, MPI_INT, lengths.data(), 1, MPI_INT, root_, communicator_));
    std::size_t total = 0;
    if (rank_ == root_) {
        for (std::size_t index = 0; index < lengths.size(); ++index) {
            offsets[index] = static_cast<int>(total);
            total += static_cast<std::size_t>(lengths[index]);
            if (total > maxWireBytes_) { failed = 1; break; }
        }
    }
    checked(MPI_Bcast(&failed, 1, MPI_INT, root_, communicator_));
    if (failed) throw std::length_error("MPI batch output exceeds wire budget");
    std::string gathered(rank_ == root_ ? total : 0, '\0');
    checked(MPI_Gatherv(encoded.data(), length, MPI_CHAR, gathered.data(), lengths.data(),
                        offsets.data(), MPI_CHAR, root_, communicator_));
    if (rank_ != root_) return {};
    std::vector<TaskResult> output(tasks.size());
    for (int worker = 0; worker < ranks_; ++worker) {
        const auto results = decodeResults(std::string_view(gathered).substr(
            static_cast<std::size_t>(offsets[worker]), static_cast<std::size_t>(lengths[worker])),
            maxWireBytes_);
        std::size_t index = static_cast<std::size_t>(worker);
        for (const auto& result : results) {
            if (index >= tasks.size() || result.id != tasks[index].id)
                throw std::runtime_error("MPI worker returned mismatched task identities");
            output[index] = result;
            index += static_cast<std::size_t>(ranks_);
        }
        if (index < tasks.size()) throw std::runtime_error("MPI worker returned incomplete results");
    }
    return output;
}

} // namespace xolver::parallel
#endif
