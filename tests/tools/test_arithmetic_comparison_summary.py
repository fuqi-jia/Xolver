import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/remote'))
from summarize_arithmetic_comparison import summarize


class ArithmeticComparisonSummary(unittest.TestCase):
    def row(self, index=0):
        return dict(index=index, case=dict(sha256=str(index), logic='QF_NIA', member='case'),
                    binaries={n: dict(path=n, sha256=n) for n in ('baseline', 'candidate', 'z3')},
                    manifest_sha256='fixed', timeout=60, memory_bytes=16 * 1024**3,
                    wrong_verdict=False, observations={n: dict(result='sat', seconds=1, cpu=3)
                        for n in ('baseline', 'candidate', 'z3')})

    def report(self, rows):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for row in rows:
                target = root / ('case-' + str(row['index']))
                target.mkdir()
                (target / 'report.json').write_text(json.dumps(row))
            return summarize(root, len(rows))

    def test_sat_requires_truth_evidence_then_shares_that_same_hashed_truth(self):
        row = self.row()
        result = self.report([row])
        self.assertEqual(result['counts']['candidate']['verified_decided'], 0)
        row['observations']['candidate']['replay'] = dict(result='sat')
        result = self.report([row])
        for solver in ('baseline', 'candidate', 'z3'):
            self.assertEqual(result['counts'][solver]['verified_decided'], 1)

    def test_two_xolver_versions_do_not_independently_confirm_unsat(self):
        row = self.row()
        for solver in ('baseline', 'candidate'):
            row['observations'][solver]['result'] = 'unsat'
        row['observations']['z3']['result'] = 'timeout'
        result = self.report([row])
        self.assertEqual(result['counts']['candidate']['verified_decided'], 0)
        row['observations']['candidate']['unsat_check'] = dict(result='unsat')
        result = self.report([row])
        self.assertEqual(result['counts']['candidate']['verified_decided'], 1)
        self.assertEqual(result['counts']['z3']['verified_decided'], 0)

    def test_mixed_binaries_and_budgets_are_rejected(self):
        for field in ('binaries', 'timeout'):
            first, second = self.row(), self.row(1)
            if field == 'binaries':
                second[field]['candidate']['sha256'] = 'changed'
            else:
                second[field] = 30
            with self.assertRaisesRegex(ValueError, 'mixed protocol'):
                self.report([first, second])

    def test_budget_overruns_cannot_be_scored_as_solver_gains(self):
        for nested in (None, 'model', 'replay', 'unsat_check'):
            row = self.row()
            observation = row['observations']['baseline']
            if nested:
                observation[nested] = dict(result='timeout', seconds=286)
            else:
                observation.update(result='timeout', seconds=286)
            with self.assertRaisesRegex(ValueError, 'wall budget overrun'):
                self.report([row])
        row = self.row()
        row['protocol_errors'] = [dict(label='candidate', budget_overrun=True)]
        with self.assertRaisesRegex(ValueError, 'wall budget overrun'):
            self.report([row])

    def test_different_model_capture_protocols_cannot_be_combined(self):
        first, second = self.row(), self.row(1)
        second['model_capture'] = 'initial-solve'
        with self.assertRaisesRegex(ValueError, 'mixed protocol.*model_capture'):
            self.report([first, second])

    def test_single_model_and_legacy_duplicate_capture_cannot_be_combined(self):
        first, second = self.row(), self.row(1)
        first['model_capture'] = 'initial-solve'
        second['model_capture'] = 'initial-solve-single-model'
        with self.assertRaisesRegex(ValueError, 'mixed protocol.*model_capture'):
            self.report([first, second])

    def test_invalid_exported_model_is_not_hidden_by_an_agreeing_verdict(self):
        row = self.row()
        row['observations']['candidate']['replay'] = dict(result='unsat')
        result = self.report([row])
        self.assertEqual(result['invalid_exported_models'], [dict(index=0, solver='candidate')])
        self.assertEqual(result['counts']['candidate']['verified_decided'], 0)

    def test_opposite_verdicts_are_rejected_even_if_driver_did_not_flag_them(self):
        row = self.row()
        row['observations']['candidate']['replay'] = dict(result='sat')
        row['observations']['baseline']['result'] = 'unsat'
        result = self.report([row])
        self.assertEqual(result['wrong_verdicts'], [0])
        self.assertEqual(result['counts']['candidate']['verified_decided'], 0)

    def test_bad_model_still_fails_when_another_solver_supplies_a_checked_witness(self):
        row = self.row()
        row['observations']['candidate']['replay'] = dict(result='unsat')
        row['observations']['z3']['replay'] = dict(result='sat')
        result = self.report([row])
        self.assertEqual(result['counts']['candidate']['verified_decided'], 0)
        self.assertEqual(result['counts']['z3']['verified_decided'], 1)


if __name__ == '__main__':
    unittest.main()
