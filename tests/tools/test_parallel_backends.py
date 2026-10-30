"""End-to-end named tasks; optional frameworks run only when explicitly requested."""
import argparse
import json
import os
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "python"))

WORKER = None
BACKENDS = ()


class ParallelTests(unittest.TestCase):
    def test_protocol_validation(self):
        from xolver_parallel import Task
        from xolver_parallel.protocol import decode_results, encode_tasks
        task = Task("binary", "echo", bytes([0, 128, 255]))
        self.assertEqual(json.loads(encode_tasks([task]))["tasks"][0]["payload"], [0, 128, 255])
        for version in (True, 1.0, 2):
            with self.assertRaises(ValueError):
                decode_results(json.dumps({"version": version, "results": []}).encode(), [])
        for payload in ([-1], [256], [True], [1.5], None):
            with self.assertRaises(ValueError):
                decode_results(json.dumps({"version": 1, "results": [
                    {"id": task.id, "ok": True, "payload": payload, "error": ""}]}).encode(), [task])

    def test_disabled_frameworks_do_not_import_dependencies(self):
        from xolver_parallel import DaskExecutor, SparkExecutor, Worker, compiled_backends
        for name, constructor in (("dask", DaskExecutor), ("spark", SparkExecutor)):
            if name not in compiled_backends():
                with self.assertRaises(RuntimeError):
                    constructor(None, Worker(("unused",)))
                self.assertNotIn("distributed" if name == "dask" else "pyspark", sys.modules)

    def exercise(self, executor):
        from xolver_parallel import Task
        binary = bytes([0, 128, 255])
        source = "(set-logic QF_LIA)(declare-const x Int)(assert (> x 2))(check-sat)"
        request = json.dumps({"smt2": source, "model": True}).encode()
        result = executor.map([Task("binary", "echo", binary), Task("sat", "smt.solve", request),
                               Task("error", "missing-handler")])
        self.assertEqual(result[0].get(), binary)
        model = json.loads(result[1].get())
        self.assertEqual(model["result"], "sat")
        self.assertEqual(model["model_validation"], "satisfied")
        with self.assertRaises(RuntimeError):
            result[2].get()
        unsat = json.dumps({"smt2": "(set-logic QF_LIA)(assert false)(check-sat)"}).encode()
        self.assertEqual(json.loads(executor.submit(Task("unsat", "smt.solve", unsat)).result().get())["result"], "unsat")
        self.assertEqual(executor.map([]), [])

    def test_local(self):
        if not WORKER:
            self.skipTest("native worker is not specified")
        from xolver_parallel import LocalExecutor, Worker
        with LocalExecutor(Worker((WORKER,)), workers=2) as executor:
            self.exercise(executor)

    def test_persistent_solver_tasks_isolate_declarations_and_failures(self):
        if not WORKER:
            self.skipTest("native worker is not specified")
        from xolver_parallel import Task, Worker, WorkerSession
        with WorkerSession(Worker((WORKER,))) as session:
            pid = None
            # Same name, different sorts/assertions: no state may cross tasks.
            for index, (body, expected) in enumerate([
                    ('(declare-const x Int)(assert (> x 2))', 'sat'),
                    ('(declare-const x Bool)(assert x)(assert (not x))', 'unsat'),
                    ('(declare-const x Int)(assert (= x 0))', 'sat')]):
                task = Task(str(index), 'smt.solve', json.dumps(dict(
                    smt2='(set-logic ALL)' + body + '(check-sat)')).encode())
                result = session.run([task])[0]
                self.assertEqual(json.loads(result.get())['result'], expected)
                current = session.channel.process.pid
                if pid is not None:
                    self.assertEqual(current, pid)
                pid = current
                with self.assertRaises(RuntimeError):
                    session.run([Task('missing', 'missing-handler')])[0].get()
            self.assertEqual(session.run([]), [])
        self.assertEqual(session.channel.process.returncode, 0)

    def test_dask(self):
        if "dask" not in BACKENDS:
            self.skipTest("Dask not requested")
        from distributed import Client, LocalCluster
        from xolver_parallel import DaskExecutor, Worker
        with LocalCluster(n_workers=2, threads_per_worker=1, processes=True, dashboard_address=None,
                          memory_limit=0) as cluster, Client(cluster) as client:
            self.exercise(DaskExecutor(client, Worker((WORKER,))))

    def test_spark(self):
        if "spark" not in BACKENDS:
            self.skipTest("Spark not requested")
        from pyspark import SparkConf, SparkContext
        from xolver_parallel import SparkExecutor, Worker
        config = SparkConf().set("spark.executorEnv.PYTHONPATH", os.environ.get("PYTHONPATH", "")).setMaster("local[1]").setAppName("xolver-parallel-test").set("spark.ui.enabled", "false")
        with SparkContext(conf=config) as context:
            with SparkExecutor(context, Worker((WORKER,)), partitions=2) as executor:
                self.exercise(executor)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--package", type=Path, required=True)
    parser.add_argument("--worker", required=True)
    parser.add_argument("--backends", nargs="*", default=[])
    args = parser.parse_args()
    sys.path.insert(0, str(args.package))
    os.environ["PYTHONPATH"] = str(args.package.resolve()) + os.pathsep + os.environ.get("PYTHONPATH", "")
    WORKER, BACKENDS = str(Path(args.worker).resolve()), tuple(args.backends)
    unittest.main(argv=[sys.argv[0]], verbosity=2)
