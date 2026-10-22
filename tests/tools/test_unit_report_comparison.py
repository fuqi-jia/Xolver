import importlib.util
from pathlib import Path
import tempfile
import unittest
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("compare_unit_reports", ROOT / "tools/remote/compare_unit_reports.py")
reports = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reports)


def report(cases, failures=0):
    return ('<testsuites><testsuite tests="8" failures="' + str(failures) + '" errors="0">'
            + cases + '</testsuite></testsuites>\n')


PASS = '<testcase classname="unit.cpp" name="A" status="run"/>'
FAIL = '<testcase classname="unit.cpp" name="A" status="run"><failure/></testcase>'


class UnitReportComparison(unittest.TestCase):
    def compare(self, baseline, candidate, before_rc=0, after_rc=0, minimum=1):
        with tempfile.TemporaryDirectory() as directory:
            before, after = (Path(directory) / n for n in ('before.xml', 'after.xml'))
            before.write_text(baseline); after.write_text(candidate)
            return reports.compare(before, after, before_rc, after_rc, minimum)

    def test_legacy_stdout_diagnostics_preserve_complete_results(self):
        text = '<?xml version="1.0"?>\nlegacy diagnostic <not XML\n' + report(PASS)
        result = self.compare(text, text)
        self.assertEqual(result['metrics'], {'full_units_complete': 1, 'new_unit_failures': 0})
        self.assertGreater(result['candidate']['diagnostic_prefix_bytes'], 0)

    def test_known_failures_remain_visible(self):
        result = self.compare(report(FAIL, 1), report(FAIL, 1), 1, 1)
        self.assertEqual(result['candidate']['failures'][0]['count'], 1)
        self.assertEqual(result['metrics']['new_unit_failures'], 0)

    def test_new_failure_is_a_regression(self):
        self.assertEqual(self.compare(report(PASS), report(FAIL, 1), 0, 1)['metrics']['new_unit_failures'], 1)

    def test_repeated_subcase_identities_are_counted(self):
        self.assertEqual(self.compare(report(PASS * 2), report(PASS * 2))['candidate']['cases_including_subcases'], 2)
        with self.assertRaisesRegex(ValueError, 'multiplicities'):
            self.compare(report(PASS * 2), report(PASS))

    def test_timeout_or_crash_cannot_pass_with_xml(self):
        for rc in (124, 137, -11, 2):
            with self.subTest(rc=rc), self.assertRaisesRegex(ValueError, 'did not complete'):
                self.compare(report(PASS), report(PASS), 0, rc)

    def test_missing_or_truncated_report_rejected(self):
        for text in ('legacy diagnostic only\n', '<testsuites><testsuite>'):
            with self.subTest(text=text), self.assertRaises((ValueError, ET.ParseError)):
                self.compare(report(PASS), text)

    def test_extra_report_rejected(self):
        with self.assertRaisesRegex(ValueError, 'one complete'):
            self.compare(report(PASS), report(PASS) * 2)

    def test_missing_test_cases_rejected(self):
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            self.compare(report(PASS), report(PASS), minimum=2)

    def test_exit_and_failure_totals_must_agree(self):
        with self.assertRaisesRegex(ValueError, 'exit status'):
            self.compare(report(PASS), report(FAIL, 1))
        with self.assertRaisesRegex(ValueError, 'failure totals'):
            self.compare(report(PASS), report(FAIL), 0, 1)

    def test_skipped_case_rejected(self):
        with self.assertRaisesRegex(ValueError, 'not run'):
            self.compare(report(PASS), report(PASS.replace('/>', '><skipped/></testcase>')))


if __name__ == '__main__':
    unittest.main()
