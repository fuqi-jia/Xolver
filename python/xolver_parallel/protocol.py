"""Portable named tasks shared by local, MPI, Spark and Dask workers."""
from dataclasses import dataclass
import json
from typing import List, Sequence


@dataclass(frozen=True)
class Task:
    id: str
    handler: str
    payload: bytes = b""

    def __post_init__(self):
        if not isinstance(self.id, str) or not isinstance(self.handler, str):
            raise TypeError("task identifiers and handler names must be strings")
        if not isinstance(self.payload, bytes):
            raise TypeError("task payload must be bytes")


@dataclass(frozen=True)
class TaskResult:
    id: str
    success: bool
    payload: bytes = b""
    error: str = ""

    def get(self) -> bytes:
        if not self.success:
            raise RuntimeError(self.error)
        return self.payload


def encode_tasks(tasks: Sequence[Task]) -> bytes:
    return json.dumps({"version": 1, "tasks": [
        {"id": task.id, "handler": task.handler, "payload": list(task.payload)}
        for task in tasks]}).encode("utf-8")


def decode_results(data: bytes, tasks: Sequence[Task]) -> List[TaskResult]:
    root = json.loads(data)
    if not isinstance(root, dict) or type(root.get("version")) is not int or root.get("version") != 1:
        raise ValueError("invalid worker protocol version")
    records = root.get("results")
    if not isinstance(records, list) or len(records) != len(tasks):
        raise ValueError("worker returned incomplete results")
    results = []
    for task, record in zip(tasks, records):
        if not isinstance(record, dict) or record.get("id") != task.id or type(record.get("ok")) is not bool:
            raise ValueError("worker returned mismatched task identities or status")
        payload = record.get("payload")
        if not isinstance(payload, list) or any(type(v) is not int or v < 0 or v > 255 for v in payload):
            raise ValueError("worker returned an invalid byte array")
        if not isinstance(record.get("error"), str):
            raise ValueError("worker returned an invalid error message")
        results.append(TaskResult(task.id, record["ok"], bytes(payload), record["error"]))
    return results
