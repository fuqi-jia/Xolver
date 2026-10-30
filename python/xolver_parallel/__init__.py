"""Optional distributed task clients for the Xolver worker protocol."""
from .protocol import Task, TaskResult
from .executors import Worker, LocalExecutor, DaskExecutor, SparkExecutor, compiled_backends
from .session import WorkerSession

__all__ = ["Task", "TaskResult", "Worker", "WorkerSession", "LocalExecutor", "DaskExecutor", "SparkExecutor", "compiled_backends"]
