"""Framework adapters; importing this module imports no optional framework."""
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import json
import math
from pathlib import Path
from typing import Sequence, Tuple

from .protocol import Task
from .session import WorkerSession


def compiled_backends():
    features = json.loads(Path(__file__).with_name("_build_features.json").read_text())
    return ("local",) + tuple(name for name, enabled in features.items() if enabled)


def _require(name):
    if name not in compiled_backends():
        raise RuntimeError("backend '{}' is disabled; configure with -DXOLVER_ENABLE_{}=ON".format(name, name.upper()))


@dataclass(frozen=True)
class Worker:
    # The executable and its dependencies must be deployed on each worker node.
    # Pass an argument vector; commands are never interpreted by a shell.
    argv: Tuple[str, ...]
    timeout: float = 60.0
    max_bytes: int = 64 * 1024 * 1024

    def __post_init__(self):
        if isinstance(self.argv, (str, bytes)) or not self.argv or any(not isinstance(s, str) for s in self.argv):
            raise TypeError("worker argv must be a nonempty sequence of strings")
        object.__setattr__(self, "argv", tuple(self.argv))
        if not math.isfinite(self.timeout) or self.timeout <= 0 or type(self.max_bytes) is not int or self.max_bytes <= 0:
            raise ValueError("worker timeout and message budget must be positive")

    def run(self, tasks: Sequence[Task]):
        with WorkerSession(self) as session:
            return session.run(tasks)


def _one(worker, task):
    return worker.run([task])[0]


def _partition(worker, items):
    # Bounded batches avoid materializing an entire Spark partition at once.
    with WorkerSession(worker) as session:
        batch = []
        for index, task in items:
            batch.append((index, task))
            if len(batch) == 32:
                for (index, _), result in zip(batch, session.run([task for _, task in batch])):
                    yield index, result
                batch = []
        if batch:
            for (index, _), result in zip(batch, session.run([task for _, task in batch])):
                yield index, result


class LocalExecutor:
    def __init__(self, worker: Worker, workers=1):
        self.worker = worker
        self.pool = ThreadPoolExecutor(max_workers=workers)

    def submit(self, task: Task):
        return self.pool.submit(_one, self.worker, task)

    def map(self, tasks: Sequence[Task]):
        return [future.result() for future in [self.submit(task) for task in tasks]]

    def close(self):
        self.pool.shutdown(wait=True)

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()


class DaskExecutor:
    def __init__(self, client, worker: Worker):
        _require("dask")
        self.client, self.worker = client, worker

    def submit(self, task: Task):
        # Solver work may repeat across submissions; disable Dask's pure-call
        # deduplication so callers retain explicit task identity and lifetime.
        return self.client.submit(_one, self.worker, task, pure=False)

    def map(self, tasks: Sequence[Task]):
        return self.client.gather([self.submit(task) for task in tasks])


class SparkExecutor:
    def __init__(self, context, worker: Worker, partitions=None):
        _require("spark")
        if partitions is not None and partitions <= 0:
            raise ValueError("Spark partition count must be positive")
        self.context, self.worker, self.partitions = context, worker, partitions
        self.pool = ThreadPoolExecutor(max_workers=1)

    def map(self, tasks: Sequence[Task]):
        if not tasks:
            return []
        worker = self.worker
        count = self.partitions or self.context.defaultParallelism
        records = self.context.parallelize(list(enumerate(tasks)), count).mapPartitions(
            lambda items: _partition(worker, items)).collect()
        if sorted(index for index, _ in records) != list(range(len(tasks))):
            raise ValueError("Spark returned duplicate or missing task results")
        return [result for _, result in sorted(records, key=lambda item: item[0])]

    def submit(self, task: Task):
        return self.pool.submit(lambda: self.map([task])[0])

    def close(self):
        self.pool.shutdown(wait=True)

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()
