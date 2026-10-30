# Parallel execution API

`Executor` schedules arbitrary C++ callables and returns typed `std::future`
results. It has no solver or theory dependency; a different scheduling backend
can implement its protected `enqueue` operation. Accepted tasks execute exactly
once. Task exceptions reach `future::get()`.

```cpp
#include "parallel/ThreadPool.h"

xolver::parallel::ThreadPool pool(2);
auto result = pool.submit([](int x) { return x * x; }, 7);
auto value = result.get(); // 49
pool.waitIdle();
```

The width is explicit and defaults to one. Choose it from the caller's allocated
CPUs; workers inherit the process affinity. Arguments are copied or moved; use
`std::ref` for shared references and synchronize shared mutable state yourself.
Callables can capture a `std::stop_token` for cooperative cancellation.

`close()` rejects later submissions and drains accepted work. Destruction joins
all workers. Manage pool lifetime outside its own tasks, and do not block on
nested tasks in an exhausted pool. `waitIdle()` detects calls from its own
workers and throws instead of waiting for itself.

Link `xolver_core`. The combined runnable example is:

```sh
cmake --build build --target xolver-api-examples
./build/bin/xolver-api-examples
```

## Optional backends

All six options default to `OFF`: `XOLVER_ENABLE_MPI`, `SPARK`, `DASK`, `CUDA`,
`HIP`, `OPENACC`. Disabled backends neither search for nor link their SDKs.
Enable only installed dependencies, using the same build directory:

```sh
cmake -S . -B build -DXOLVER_ENABLE_MPI=ON -DXOLVER_ENABLE_OPENACC=ON
cmake --build build --target xolver-parallel-examples xolver-parallel-worker
mpirun -n 2 ./build/bin/xolver-parallel-examples mpi
./build/bin/xolver-parallel-examples openacc
```

MPI supports standard implementations including OpenMPI. Every rank installs
its own `TaskRegistry` and collectively calls `MpiExecutor::run`; only the chosen
root supplies tasks and receives ordered results. Names and byte payloads cross
processes; captured lambdas and pointers do not. Keep collective ordering and
root consistent, and destroy the executor before `MPI_Finalize`.

`DeviceExecutor` supplies worker-local allocation, copy, fill, synchronization
and native CUDA/HIP stream or OpenACC queue access. Submit kernels through its
context; initialization and execution errors reach futures. Compose it inside
MPI task handlers for hybrid execution (example: `mpi cuda`). GPU SDKs and
hardware are required for GPU execution. OpenACC can select a host device, which
the example reports explicitly. This API does not port SMT search to GPU kernels.

## Spark, Dask and worker protocol

Enable `XOLVER_ENABLE_SPARK`/`DASK` with `Python3_EXECUTABLE` pointing to an
interpreter containing `pyspark`/`distributed`. Spark also needs Java. Use the
configured package under `build/python`, which records enabled backends:

```python
from xolver_parallel import Task, Worker, DaskExecutor
worker = Worker(("/absolute/path/xolver-parallel-worker",))
executor = DaskExecutor(client, worker)  # caller owns the Dask client
result = executor.submit(Task("demo", "echo", b"hello")).result().get()
```

`SparkExecutor(context, worker, partitions=N)` accepts an existing SparkContext;
`LocalExecutor(worker, workers=N)` uses local processes. Framework workers must
have the executable, libraries and configured Python package deployed. Framework
retries can execute a task again: distributed handlers must be idempotent.

The CLI worker accepts successive length-framed JSON version-1 batches and writes
one ordered result frame per batch; diagnostics use stderr. Each frame is an
8-byte unsigned big-endian length followed by 1 byte to 64 MiB of JSON. EOF is valid
only between frames. `WorkerSession(worker)` keeps a POSIX worker process open
across calls to `run(tasks)`; use it as a context manager. Calls serialize and
share a wall deadline covering encoding, startup and transport. Timeout or a
protocol error closes the process group. Spark reuses a session per partition.
Built-in handlers are `echo`,
`backends`, and `smt.solve`. The latter accepts JSON bytes containing `smt2`,
`timeout_ms` (default 60000) and `model` (default false), and solves the public
API's final query snapshot with a fresh solver for each task, including repeated
tasks. A requested model includes its validation status;
`indeterminate` is not a verified witness. Custom applications register their own
handlers. Task errors remain separate from solver `unknown` results.

Backend references: [MPI discovery](https://cmake.org/cmake/help/latest/module/FindMPI.html),
[OpenACC discovery](https://cmake.org/cmake/help/latest/module/FindOpenACC.html),
[Dask Client](https://distributed.dask.org/en/latest/client.html),
[Spark parallelize](https://spark.apache.org/docs/latest/api/python/reference/pyspark.SparkContext.parallelize.html).
