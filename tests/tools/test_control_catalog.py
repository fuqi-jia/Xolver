"""Check names and reader modes independently of the C++ build."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/governance"))
try:
    spec = importlib.util.spec_from_file_location(
        "control_catalog_audit", ROOT / "tools/governance/control_catalog.py")
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
finally:
    sys.path.pop(0)


def control(name="XOLVER_TEST", *kinds):
    return {"name": name, "reads": [{"kind": kind} for kind in kinds or ("Flag",)]}


class ControlCatalogTests(unittest.TestCase):
    def validate(self, source, controls=None, extra_files=None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            files = {
                "src/base/controls.json": json.dumps({"controls": controls if controls is not None
                                                       else [control()]}),
                "src/search/Example.cpp": source,
            }
            files.update(extra_files or {})
            for name, text in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            return audit.validate(root)

    def test_all_qualifications_and_comments_preserve_source_locations(self):
        report = self.validate('''// read<ReadKind::Presence>("XOLVER_GHOST")
auto a = config::read<config::ReadKind::Flag>("XOLVER_TEST");
auto b = xolver::config::read<xolver::config::ReadKind::Flag>(
    /* name */ "XOLVER_TEST", true);
/* read<ReadKind::Flag>("XOLVER_OLD"); */
auto c = read<ReadKind::Flag>("XOLVER_TEST");
''')
        self.assertEqual(report["unique_controls"], 1)
        self.assertEqual(report["literal_read_sites"], 3)
        self.assertEqual([s["line"] for s in report["controls"][0]["sites"]], [2, 3, 6])

    def test_quoted_example_is_not_a_call(self):
        source = 'const char* example = "read<ReadKind::Flag>(variable)";\n'
        source += 'auto x = read<ReadKind::Flag>("XOLVER_TEST");'
        self.assertEqual(self.validate(source)["literal_read_sites"], 1)

    def test_multiple_modes_are_explicit(self):
        source = 'read<ReadKind::Flag>("XOLVER_TEST"); read<ReadKind::Presence>("XOLVER_TEST");'
        report = self.validate(source, [control("XOLVER_TEST", "Flag", "Presence")])
        self.assertTrue(report["controls"][0]["mixed_reader_semantics"])

    def test_unknown_name_and_mismatched_type_rejected(self):
        for source in ('read<ReadKind::Flag>("XOLVER_TYPO");',
                       'read<ReadKind::Presence>("XOLVER_TEST");',
                       'read<ReadKind::Int>("XOLVER_TEST", 2);'):
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, "undeclared or mismatched"):
                self.validate(source)

    def test_dynamic_names_and_string_concatenation_rejected(self):
        for argument in ('name', '"XOLVER_" "TEST"', '"XOLVER_TEST" + suffix'):
            with self.subTest(argument=argument), self.assertRaisesRegex(ValueError, "literal names"):
                self.validate(f'read<ReadKind::Flag>({argument});')

    def test_unused_declaration_rejected(self):
        with self.assertRaisesRegex(ValueError, "no reader"):
            self.validate('// read<ReadKind::Flag>("XOLVER_TEST");')

    def test_duplicate_name_or_read_mode_rejected(self):
        for controls in ([control(), control()], [control("XOLVER_TEST", "Flag", "Flag")]):
            with self.subTest(controls=controls), self.assertRaisesRegex(ValueError, "duplicate"):
                self.validate('', controls)

    def test_invalid_read_contract_rejected(self):
        for entry in (control("XOLVER_TEST", "Text"),
                      {"name": "XOLVER_TEST", "reads": []},
                      {**control(), "legacy_text": True},
                      {"name": "XOLVER_TEST", "reads": [{"kind": "Flag", "key": "kOLD"}]}):
            with self.subTest(entry=entry), self.assertRaises(ValueError):
                self.validate('', [entry])

    def test_global_header_and_old_key_call_rejected(self):
        with self.assertRaisesRegex(ValueError, "global ControlCatalog"):
            self.validate('', extra_files={"src/base/ControlCatalog.h": "#pragma once"})
        for source in ('config::read(config::control::kXOLVER_TEST);',
                       'read(control::kXOLVER_TEST);'):
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, "literal names"):
                self.validate(source)

    def test_untyped_literal_reader_rejected(self):
        with self.assertRaisesRegex(ValueError, "undeclared or mismatched"):
            self.validate('env::flag("XOLVER_TEST");')


if __name__ == "__main__":
    unittest.main()
