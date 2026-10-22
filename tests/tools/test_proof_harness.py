import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class ProofHarnessContract(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.solver = self.root / "fake-solver"
        self.checker = self.root / "fake-checker"
        self.solver.write_text("""#!/usr/bin/env python3
import pathlib, sys
source = pathlib.Path(sys.argv[2]).read_text()
print('unsat')
if 'crash' in source: sys.exit(1)
base = sys.argv[sys.argv.index('--produce-proof') + 1]
if 'no-proof' not in source:
    pathlib.Path(base + '.cnf').write_text('c xolver-proof: 1 original clauses, 0 theory lemmas assumed as axioms\\np cnf 0 1\\n0\\n')
    pathlib.Path(base + '.drat').write_text('0\\n')
""")
        self.checker.write_text("#!/bin/sh\nprintf '\\rs VERIFIED\\n'\n")
        self.solver.chmod(0o755)
        self.checker.chmod(0o755)

    def run_corpus(self, sources):
        manifest = self.root / "list.txt"
        manifest.write_text(''.join(str(p) + '\n' for p in sources))
        env = dict(os.environ, XOLVER_PROOF_WORKDIR=str(self.root / "evidence"))
        return subprocess.run(
            ['bash', str(ROOT / 'tools/proof/run_proof_corpus.sh'), str(self.solver),
             str(self.checker), str(manifest)], env=env, capture_output=True,
            text=True, timeout=15)

    def test_missing_or_empty_corpus_cannot_pass(self):
        self.assertNotEqual(self.run_corpus([]).returncode, 0)
        self.assertNotEqual(self.run_corpus([self.root / 'missing.smt2']).returncode, 0)

    def test_solver_crash_is_not_a_skip(self):
        case = self.root / 'crash.smt2'
        case.write_text('; crash\n(set-info :status unsat)\n')
        result = self.run_corpus([case])
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn('ERROR=1', result.stdout)

    def test_malformed_checker_success_marker_is_rejected(self):
        self.checker.write_text("#!/bin/sh\nprintf 's VERIFIEDgarbage\\n'\n")
        case = self.root / 'input.smt2'
        case.write_text('(set-info :status unsat)\n')
        result = self.run_corpus([case])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('REJECTED=1', result.stdout)

    def test_same_basename_cannot_reuse_another_proof(self):
        files = []
        for directory, text in [('a', ''), ('b', '; no-proof\n')]:
            folder = self.root / directory
            folder.mkdir()
            case = folder / 'same.smt2'
            case.write_text(text + '(set-info :status unsat)\n')
            files.append(case)
        result = self.run_corpus(files)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('VERIFIED(complete)=1', result.stdout)
        self.assertIn('NO-PROOF(degraded)=1', result.stdout)


if __name__ == '__main__':
    unittest.main()
