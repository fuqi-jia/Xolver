import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]


def load(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


benchmark = load('audit_benchmark', 'tools/regression/run_benchmark.py')
comparison = load('audit_comparison', 'tools/differential/compare_solvers.py')
fuzz = load('audit_combination_fuzz', 'tools/fuzz/fuzz_combination_soundness.py')


class EvidenceReaders(unittest.TestCase):
    def test_benchmark_uses_stdout_and_exit_status(self):
        self.assertEqual(benchmark.parse_result('sat\n', 'unsat\n', 0), 'sat')
        self.assertEqual(benchmark.parse_result('sat\n', '', 1), 'error')
        self.assertEqual(benchmark.parse_result('', 'sat\n', 0), 'error')
        self.assertEqual(benchmark.parse_result('sat garbage\n', '', 0), 'error')

    def test_comparison_accepts_only_complete_stdout_lines(self):
        self.assertEqual(comparison.parse_verdict('sat\n', 'unsat\n'), 'sat')
        self.assertEqual(comparison.parse_verdict('(error "sat")\n', ''), '')
        self.assertEqual(comparison.parse_verdict('', 'sat\n'), '')

    def test_fuzzer_does_not_turn_errors_into_answers(self):
        base = [sys.executable, '-c']
        self.assertEqual(fuzz.run(base + ["print('sat'); raise SystemExit(1)"], '', 5), 'error')
        self.assertEqual(fuzz.run(base + ["import sys; print('sat', file=sys.stderr)"], '', 5), 'error')
        self.assertEqual(fuzz.run(base + ["print('sat')"], '', 5), 'sat')


if __name__ == '__main__':
    unittest.main()
