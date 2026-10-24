import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.analyze_qcp_corpus import fingerprint
from tools.integration.select_qcp_holdout import choose
from tools.regression.select_public_sample import select
from tools.regression.compare_fixed_sample import summarize


class BenchmarkSelectionTests(unittest.TestCase):
    def test_family_sampling_does_not_select_by_status(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            for family in ['one', 'two', 'three']:
                for index in range(3):
                    p = root / 'QF_NIA' / family / f'{index}.smt2'
                    p.parent.mkdir(parents=True, exist_ok=True)
                    p.write_text('(set-info :status sat)\n(assert true)')
            first = select(root, {'QF_NIA': 3})
            self.assertEqual({c['family'] for c in first['cases']}, {'one','two','three'})
            for p in root.rglob('*.smt2'):
                p.write_text('(set-info :status unsat)\n(assert false)')
            second = select(root, {'QF_NIA': 3})
            self.assertEqual([c['member'] for c in first['cases']], [c['member'] for c in second['cases']])
            self.assertNotEqual(first['cases'][0]['sha256'], second['cases'][0]['sha256'])

    def test_qcp_holdout_excludes_family_name_and_byte_duplicates(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            sources = ['dev/a.c','other/a.c','copy/c.c','new/d.c','last/e.c']
            lines = []
            for i, source in enumerate(sources):
                p = root/source;p.parent.mkdir(parents=True,exist_ok=True)
                p.write_text('development' if i in (0,2) else str(i))
                lines.append('linux-binary/symexec --input-file='+source+';')
            (root/'run-example-linux.sh').write_text('\n'.join(lines))
            dev={'programs':[{'source':sources[0],'source_sha256':hashlib.sha256(b'development').hexdigest()}]}
            report=choose(root,dev,2)
            self.assertEqual({c['source'] for c in report['selected']},{'new/d.c','last/e.c'})

    def test_alpha_hash_preserves_constants_sorts_and_premises(self):
        a='(declare-const |x| Int)(assert (>= |x| 0))(assert (not (<= |x| 5)))'
        b=a.replace('|x|','|renamed|')
        self.assertEqual(fingerprint(a),fingerprint(b))
        self.assertNotEqual(fingerprint(a),fingerprint(a.replace(' 5',' 6')))
        self.assertNotEqual(fingerprint(a),fingerprint(a.replace('(assert (>= |x| 0))','')))

    def test_timeouts_and_unknowns_are_not_latency_wins(self):
        def pair(a,b,z):return {n:dict(result=r,seconds=1.0) for n,r in [('baseline',a),('candidate',b),('z3',z)]}
        rows=[dict(case={'family':'A','expected':'unsat'},observations=[pair('unknown','unsat','unsat')]),
              dict(case={'family':'B','expected':'sat'},observations=[pair('timeout','timeout','sat')])]
        report=summarize(rows,3)
        self.assertEqual(report['common_decided'],0)
        self.assertEqual(report['consistently_decided']['candidate'],1)
        self.assertEqual(report['par2_process_seconds']['baseline'],12)
        self.assertFalse(report['wrong_verdicts'])
        rows[0]['observations'][0]['candidate']['result']='sat'
        self.assertTrue(summarize(rows,3)['wrong_verdicts'])
        # An unknown reference cannot excuse a decisive contradiction between
        # implementations, or between repeated executions of one solver.
        rows=[dict(case={'family':'A','expected':'unknown'},
                   observations=[pair('sat','unsat','unknown')])]
        self.assertTrue(summarize(rows,3)['wrong_verdicts'])
        rows[0]['observations']=[pair('unknown','sat','unknown'),
                                 pair('unknown','unsat','unknown')]
        self.assertTrue(summarize(rows,3)['wrong_verdicts'])


if __name__=='__main__':unittest.main()
