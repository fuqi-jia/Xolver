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

    def multi_query_solver(self, mode):
        self.solver.write_text(f'''#!/usr/bin/env python3
import pathlib, sys
base = sys.argv[sys.argv.index('--produce-proof') + 1]
pathlib.Path(base + '.queries').write_text('2\\n')
for i in (1, 2):
    print('unsat')
    query = base + '.query-' + str(i)
    pathlib.Path(query + '.input.smt2').write_text('(set-info :status unsat)')
    if {mode!r} == 'missing' and i == 1: continue
    pathlib.Path(query + '.cnf').write_text('c xolver-proof: 1 original clauses, 0 theory lemmas assumed as axioms\\np cnf 0 1\\n0\\n')
    pathlib.Path(query + '.drat').write_text('0\\n')
''')
        case = self.root / 'multi.smt2'
        case.write_text('(check-sat)(check-sat)')
        return case

    def test_each_query_proof_is_checked(self):
        case = self.multi_query_solver('complete')
        result = self.run_corpus([case])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('query-1.input.smt2', result.stdout)
        self.assertIn('query-2.input.smt2', result.stdout)
        self.checker.write_text("#!/bin/sh\ncase \"$1\" in *query-1.cnf) exit 1;; esac\nprintf 's VERIFIED\\n'\n")
        result = self.run_corpus([case])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('REJECTED=1', result.stdout)

    def test_missing_earlier_proof_stays_degraded(self):
        result = self.run_corpus([self.multi_query_solver('missing')])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('NO-PROOF(degraded)=1', result.stdout)

    def test_missing_query_verdict_is_an_error(self):
        case = self.multi_query_solver('complete')
        self.solver.write_text(self.solver.read_text().replace("print('unsat')", "if i == 2: print('unsat')"))
        result = self.run_corpus([case])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('ERROR=1', result.stdout)


@unittest.skipUnless(os.environ.get('XOLVER_TEST_SOLVER'), 'requires the server solver')
class ProofQueryExport(unittest.TestCase):
    def test_incremental_queries_keep_separate_inputs_and_output_bases(self):
        for command, explicit in [(['solve'], True), ([], False)]:
            with self.subTest(command=command, explicit=explicit), tempfile.TemporaryDirectory() as folder:
                path = Path(folder) / 'input.smt2'
                path.write_text('(set-logic QF_UF)(declare-const p Bool)'
                                '(assert p)(check-sat)(push 1)(assert (not p))'
                                '(check-sat)(pop 1)(check-sat)')
                base = Path(folder) / 'proof' if explicit else Path(str(path) + '.proof')
                args = [os.environ['XOLVER_TEST_SOLVER'], *command, str(path), '--produce-proof']
                if explicit:
                    args.append(str(base))
                result = subprocess.run(args, capture_output=True, text=True, timeout=20)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout.splitlines(), ['sat', 'unsat', 'sat'])
                self.assertEqual(Path(str(base) + '.queries').read_text(), '3\n')
                for i in (1, 2, 3):
                    query = Path(str(base) + f'.query-{i}.input.smt2').read_text()
                    self.assertEqual(query.count('(check-sat)'), 1)
                self.assertNotIn('(assert (not p))', Path(str(base) + '.query-1.input.smt2').read_text())


if __name__ == '__main__':
    unittest.main()
