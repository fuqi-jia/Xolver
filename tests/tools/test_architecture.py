"""Negative tests for the dependency boundary checker (run on the server)."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("architecture", ROOT / "tools/governance/architecture.py")
architecture = importlib.util.module_from_spec(spec)
spec.loader.exec_module(architecture)


class ArchitectureTests(unittest.TestCase):
    def inspect(self, sources):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for name, text in sources.items():
                path = root / "src" / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            return architecture.inspect(root)[1]

    def test_reverse_dependency_rejected(self):
        errors = self.inspect({"base/Value.h": '#include "runtime/Solver.h"\n',
                               "runtime/Solver.h": "#pragma once\n"})
        self.assertTrue(any("forbidden dependency" in e for e in errors))

    def test_native_ir_allowed_without_parser_leak(self):
        self.assertEqual(self.inspect({"decision/pa/Input.h": '#include <somtparser/ir/node.h>\n'}), [])
        self.assertTrue(self.inspect({"decision/pa/Input.h": '#include <somtparser/frontend/parser.h>\n'}))

    def test_pa_cannot_reintroduce_compatibility_terms(self):
        self.assertTrue(self.inspect({"decision/pa/Input.h": "TermExpr value;\n"}))
        self.assertTrue(self.inspect({"decision/pa/Input.h": "const NativeTerms& input;\n"}))

    def test_untyped_read_rejected(self):
        self.assertTrue(self.inspect({"search/Test.cpp": 'auto v = env::flag("XOLVER_BAD");'}))

    def test_missing_old_header_rejected(self):
        self.assertTrue(self.inspect({"ir/Test.h": '#include "expr/ir.h"\n'}))

    def test_relative_path_cannot_bypass_dependency_rules(self):
        self.assertTrue(self.inspect({"base/Test.h": '#include "../search/Solver.h"\n',
                                      "search/Solver.h": "#pragma once\n"}))

    def test_retired_expression_graph_cannot_return(self):
        self.assertTrue(self.inspect({"ir/Old.h": "class CoreIr {};\n"}))
