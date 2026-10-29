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
