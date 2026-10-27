import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.qcp_backend import discharge, leased_cpu, pending_goals, proof_candidate


class QcpBackendTests(unittest.TestCase):
    def fixture(self, root):
        goals = root / 'goal.v'
        goals.write_text('''Definition safety := forall (x: Z) (H: x >= 0),
  arbitrary_heap x |-- “ x + 1 > 0 ” && “ x >= 0 ” && emp.
Definition done := forall (x: Z), x = x.
Definition unsupported := forall (xs: list Z), True.
''')
        manual = root / 'manual.v'
        manual.write_text('''Lemma proof_safety : safety. Proof. Admitted.
Lemma proof_done : done. Proof. intros. reflexivity. Qed.
Lemma proof_unsupported : unsupported. Proof. Abort.
''')
        binary = root / 'binary'
        binary.write_bytes(b'frozen executable placeholder')
        return goals, manual, binary

    def test_pending_assignment_excludes_completed_witnesses(self):
        with tempfile.TemporaryDirectory() as d:
            g, m, b = self.fixture(Path(d))
            self.assertEqual(pending_goals(m), {'safety': 'proof_safety', 'unsupported': 'proof_unsupported'})
            with patch('tools.integration.qcp_backend.leased_cpu', return_value=7):
                for assignment in ([], ['done'], ['safety', 'safety'], ['missing']):
                    with self.subTest(assignment=assignment), self.assertRaises(ValueError):
                        discharge(g, m, assignment, 'xolver', b, 60, Path(d) / 'out')

    def test_projection_unsat_only_emits_unchecked_full_statement_candidate(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            g, m, b = self.fixture(root)
            with patch('tools.integration.qcp_backend.leased_cpu', return_value=7), \
                    patch('tools.integration.qcp_backend.invoke', return_value={'result': 'unsat'}) as run:
                r = discharge(g, m, ['safety', 'unsupported'], 'xolver', b, 60, root / 'out')
            self.assertEqual(run.call_count, 2)
            self.assertEqual(r['backend_invocations'], 2)
            self.assertEqual(r['proof_candidates'], 1)
            self.assertEqual(r['verified_vcs'], 0)
            self.assertFalse(r['program_verified'])
            self.assertEqual(r['rows'][1]['status'], 'unsupported')
            candidate = Path(r['rows'][0]['candidate']).read_text()
            self.assertIn('Lemma proof_safety : safety.', candidate)
            self.assertIn('LLM_pre_process ltac:', candidate)
            self.assertNotIn('entailer!', candidate)
            self.assertNotIn('unfold ', candidate)
            self.assertNotIn('Admitted', candidate)
            self.assertNotIn('Axiom', candidate)
            self.assertFalse(r['rows'][0]['kernel_checked'])
            self.assertEqual(json.loads((root / 'out/report.json').read_text()), r)
            self.assertIn('Admitted', m.read_text())

    def test_each_condition_must_succeed_without_relabeling_sat_as_a_c_bug(self):
        for result in ('sat', 'unknown', 'timeout', 'error'):
            with self.subTest(result=result), tempfile.TemporaryDirectory() as d:
                root = Path(d)
                g, m, b = self.fixture(root)
                with patch('tools.integration.qcp_backend.leased_cpu', return_value=7), \
                        patch('tools.integration.qcp_backend.invoke', side_effect=[{'result': 'unsat'}, {'result': result}]):
                    r = discharge(g, m, ['safety'], 'z3', b, 60, root / 'out')
                self.assertEqual(r['proof_candidates'], 0)
                self.assertEqual(r['rows'][0]['status'], 'unproved')
                self.assertFalse(list((root / 'out').glob('*candidate.v')))

    def test_source_or_executable_mutation_invalidates_evidence(self):
        for role in range(3):
            with self.subTest(role=role), tempfile.TemporaryDirectory() as d:
                root = Path(d)
                g, m, b = self.fixture(root)
                def mutate(*args):
                    (g, m, b)[role].write_text('changed bytes')
                    return {'result': 'unsat'}
                with patch('tools.integration.qcp_backend.leased_cpu', return_value=7), \
                        patch('tools.integration.qcp_backend.invoke', side_effect=mutate), self.assertRaises(ValueError):
                    discharge(g, m, ['safety'], 'xolver', b, 60, root / 'out')

    def test_refuses_unleased_or_multiple_cpu_execution(self):
        for lease, affinity in [('', {7}), ('7,8', {7, 8}), ('7', {8}), ('7', {7, 8})]:
            with self.subTest(lease=lease), patch.dict(os.environ, EOS_CPU_IDS=lease), \
                    patch('os.sched_getaffinity', return_value=affinity), self.assertRaises(ValueError):
                leased_cpu()
        with patch.dict(os.environ, EOS_CPU_IDS='7'), patch('os.sched_getaffinity', return_value={7}):
            self.assertEqual(leased_cpu(), 7)

    def test_owned_cell_candidate_reconstructs_ranges_in_original_goal(self):
        candidate = proof_candidate('proof_owned', 'owned', [
            dict(address='&("left")', value='x'),
            dict(address='p', value='y + 1'),
        ])
        self.assertIn('Lemma proof_owned : owned.', candidate)
        self.assertIn('store_int_range (&("left")) (x)', candidate)
        self.assertIn('store_int_range (p) (y + 1)', candidate)
        self.assertIn('change (-2147483648 <= (y + 1) <= 2147483647)', candidate)
        self.assertIn('split_pure_spatial', candidate)
        self.assertIn('all: solve [cancel', candidate)
        self.assertNotIn('Admitted', candidate)
        self.assertNotIn('Axiom', candidate)

    def test_pure_rhs_range_candidate_does_not_require_a_spatial_conjunct(self):
        candidate = proof_candidate('proof_pure', 'pure', [
            dict(address='p', value='x'),
        ], residual_heap=False)
        self.assertIn('store_int_range (p) (x)', candidate)
        self.assertIn('split_pures; dump_pre_spatial', candidate)
        self.assertNotIn('split_pure_spatial', candidate)
        self.assertNotIn('cancel ', candidate)


if __name__ == '__main__':
    unittest.main()
