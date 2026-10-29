import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.audit_qcp_program import assess


class QcpProgramAuditTests(unittest.TestCase):
    def fixture(self, root):
        goal, auto, manual, result = [root/n for n in ['goal.v','auto.v','manual.v','result.json']]
        goal.write_text('Module Type VC_Correct. Axiom proof_a : a. Axiom proof_b : b. End VC_Correct.')
        auto.write_text('Lemma proof_a : a. Proof. Admitted.')
        manual.write_text('Lemma proof_b : b. Proof. exact I. Qed.')
        result.write_text(json.dumps(dict(returncode=0,cpu_ids='7',invocation=dict(argv=['controller.py','final-check','--run','demo']),result=dict(status='passed',phase='done',errors=[]))))
        state = root / 'state.json'
        state.write_text(json.dumps(dict(run_id='demo',phase='done',main_root=str(root),
            final_check=dict(status='passed'),target_files=dict(goal_file='goal.v',
                proof_auto_file='auto.v',proof_manual_file='manual.v'))))
        return goal, auto, manual, result, state

    def test_controller_done_does_not_prove_admitted_auto_witnesses(self):
        with tempfile.TemporaryDirectory() as d:
            g, a, m, r, state = self.fixture(Path(d))
            report = assess(g, [a,m], r, state_path=state)
            self.assertFalse(report['program_verified'])
            self.assertEqual(report['programs'], 0)
            self.assertEqual(report['verified_vcs'], 0)
            self.assertEqual(report['verification_conditions'], 2)

    def test_every_primary_witness_needs_its_original_type_and_a_complete_proof(self):
        for text in ['', 'Lemma proof_a : a. Proof. Abort.',
                     'Lemma proof_a : wrong. Proof. exact I. Qed.',
                     'Axiom proof_a : a.']:
            with self.subTest(text=text), tempfile.TemporaryDirectory() as d:
                g, a, m, r, state = self.fixture(Path(d));a.write_text(text)
                self.assertFalse(assess(g,[a,m],r, state_path=state)['program_verified'])

    def test_complete_coverage_requires_the_actual_final_checker_success(self):
        with tempfile.TemporaryDirectory() as d:
            g, a, m, r, state = self.fixture(Path(d));a.write_text('Lemma proof_a : a. Proof. exact I. Qed.')
            report = assess(g,[a,m],r, state_path=state)
            self.assertTrue(report['program_verified'])
            self.assertFalse(report['backend_qualified'])
            self.assertEqual(report['verified_vcs'],2)
            self.assertIsNone(report['external_backend_queries'])
            for change in [dict(returncode=1),dict(cpu_ids=''),dict(result=dict(status='failed',phase='done')),dict(invocation=dict(argv=['controller.py','dune-build']))]:
                original=json.loads(r.read_text());updated=dict(original,**change);r.write_text(json.dumps(updated))
                self.assertFalse(assess(g,[a,m],r, state_path=state)['program_verified']);r.write_text(json.dumps(original))

    def test_backend_qualification_links_the_same_frozen_candidates_to_checked_witnesses(self):
        import hashlib
        digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);g,a,m,r,state=self.fixture(root)
            a.write_text('Lemma proof_a : a. Proof. exact I. Qed.')
            rows=[]
            for name, source in [('a',a),('b',m)]:
                candidate=root/(name+'-candidate.v');candidate.write_text(source.read_text())
                rows.append(dict(name=name,lemma='proof_'+name,status='proof-candidate',
                    candidate=str(candidate),candidate_sha256=digest(candidate),
                    queries=[dict(result='unsat',seconds=.1)]))
            payload=dict(backend='xolver', binary=dict(sha256='frozen'),
                source_sha256=digest(g), rows=rows, timeout=60, cpu=7,
                memory_bytes=16*1024**3, protocol_errors=[])
            backend=root/'backend.json';backend.write_text(json.dumps(payload))
            report=assess(g,[a,m],r,[backend],state_path=state)
            self.assertTrue(report['backend_qualified'])
            self.assertEqual(report['external_backend_queries'],2)
            for key, value in [('timeout', 61), ('memory_bytes', 8*1024**3),
                               ('protocol_errors', [{'seconds': 61.1}])]:
                with self.subTest(key=key):
                    backend.write_text(json.dumps(dict(payload, **{key: value})))
                    invalid=assess(g,[a,m],r,[backend],state_path=state)
                    self.assertTrue(invalid['program_verified'])
                    self.assertFalse(invalid['backend_qualified'])
            backend.write_text(json.dumps(payload))
            for seconds in [60.01, float('nan')]:
                with self.subTest(seconds=seconds):
                    changed=json.loads(json.dumps(payload))
                    changed['rows'][0]['queries'][0]['seconds']=seconds
                    backend.write_text(json.dumps(changed))
                    self.assertFalse(assess(g,[a,m],r,[backend],state_path=state)['backend_qualified'])
            backend.write_text(json.dumps(payload))
            # A different reconstruction must not be labeled the same backend strategy.
            a.write_text('Lemma proof_a : a. Proof. trivial. Qed.')
            self.assertFalse(assess(g,[a,m],r,[backend],state_path=state)['backend_qualified'])

    def test_comments_and_strings_cannot_add_or_hide_proof_holes(self):
        with tempfile.TemporaryDirectory() as d:
            g, a, m, r, state = self.fixture(Path(d));a.write_text('(* Proof. Admitted. *) Lemma proof_a : a. Proof. exact I. Qed.')
            self.assertTrue(assess(g,[a,m],r, state_path=state)['program_verified'])

    def test_checked_split_queries_are_counted_without_replacing_primary_vcs(self):
        import hashlib
        digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            g, a, m, r, state = self.fixture(root)
            a.write_text('Lemma proof_a : a. Proof. exact I. Qed.')
            split = 'Lemma proof_split : split. Proof. exact I. Qed.'
            m.write_text(m.read_text() + '\n' + split)
            rows = []
            for name, block in [('a', a.read_text()),
                                ('b', 'Lemma proof_b : b. Proof. exact I. Qed.'),
                                ('split', split)]:
                candidate = root/(name+'-candidate.v'); candidate.write_text(block)
                rows.append(dict(name=name, lemma='proof_'+name, status='proof-candidate',
                    candidate=str(candidate), candidate_sha256=digest(candidate),
                    queries=[dict(result='unsat', seconds=.1)]))
            payload = dict(backend='xolver', binary=dict(sha256='frozen'),
                source_sha256=digest(g), rows=rows, timeout=60, cpu=7,
                memory_bytes=16*1024**3, protocol_errors=[])
            backend = root/'backend.json'; backend.write_text(json.dumps(payload))
            report = assess(g, [a,m], r, [backend], state_path=state)
            self.assertTrue(report['backend_qualified'])
            self.assertEqual(report['verified_vcs'], 2)
            self.assertEqual(report['external_discharged_vcs'], 2)
            self.assertEqual(report['external_auxiliary_conditions'], 1)
            self.assertEqual(report['external_backend_queries'], 3)
            payload['rows'] = rows[1:] # split cannot substitute for primary a
            backend.write_text(json.dumps(payload))
            report = assess(g, [a,m], r, [backend], state_path=state)
            self.assertTrue(report['program_verified'])
            self.assertFalse(report['backend_qualified'])
            self.assertEqual(report['external_discharged_vcs'], 1)


if __name__ == '__main__':
    unittest.main()
