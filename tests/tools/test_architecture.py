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
        self.assertEqual(self.inspect({"quantifiers/integer/Input.h": '#include <somtparser/ir/node.h>\n'}), [])
        self.assertTrue(self.inspect({"quantifiers/integer/Input.h": '#include <somtparser/frontend/parser.h>\n'}))

    def test_pa_cannot_reintroduce_compatibility_terms(self):
        self.assertTrue(self.inspect({"quantifiers/integer/Input.h": "TermExpr value;\n"}))
        self.assertTrue(self.inspect({"applications/sv/pa/Input.h": "const NativeTerms& input;\n"}))

    def test_applications_are_independent(self):
        self.assertTrue(self.inspect({
            "applications/smt/Solver.h": '#include "applications/sv/pa/Solver.h"',
            "applications/sv/pa/Solver.h": "#pragma once"}))
        self.assertTrue(self.inspect({
            "applications/sv/sl/Solver.h": '#include "applications/sv/pa/Solver.h"',
            "applications/sv/pa/Solver.h": "#pragma once"}))

    def test_logical_framework_cannot_call_an_application(self):
        self.assertTrue(self.inspect({
            "logic/first_order/Solver.h": '#include "applications/smt/Solver.h"',
            "applications/smt/Solver.h": "#pragma once"}))

    def test_search_cannot_depend_on_application(self):
        self.assertTrue(self.inspect({
            "search/Test.h": '#include "applications/smt/Solver.h"',
            "applications/smt/Solver.h": "#pragma once"}))

    def test_common_is_local_to_its_application(self):
        self.assertTrue(self.inspect({"applications/common/Test.h": "#pragma once"}))
        self.assertEqual(self.inspect({
            "applications/smt/qfnia/Private.h": '#include "applications/smt/common/Shared.h"',
            "applications/smt/common/Shared.h": "#pragma once"}), [])
        self.assertTrue(self.inspect({
            "applications/smt/common/Shared.h": '#include "applications/smt/qfnia/Private.h"',
            "applications/smt/qfnia/Private.h": "#pragma once"}))

    def test_application_base_cannot_depend_on_implementation(self):
        self.assertTrue(self.inspect({
            "applications/Solver.h": '#include "applications/smt/Private.h"',
            "applications/smt/Private.h": "#pragma once"}))

    def test_elimination_algebra_is_parser_independent(self):
        self.assertTrue(self.inspect({
            "algebra/integer/UnaryArithmetic.h": '#include <somtparser/ir/node.h>'}))

    def test_quantifiers_can_use_search_and_algebra(self):
        self.assertEqual(self.inspect({
            "quantifiers/bitvector/Eliminate.h": '#include "search/bitblast/Encode.h"\n#include "algebra/integer/Value.h"',
            "search/bitblast/Encode.h": "#pragma once",
            "algebra/integer/Value.h": "#pragma once"}), [])

    def test_search_cannot_depend_on_quantifiers(self):
        self.assertTrue(self.inspect({
            "search/sat/Test.h": '#include "quantifiers/boolean/Eliminate.h"',
            "quantifiers/boolean/Eliminate.h": "#pragma once"}))

    def test_quantifiers_cannot_depend_on_logical_or_application_driver(self):
        self.assertTrue(self.inspect({
            "quantifiers/integer/Test.h": '#include "logic/first_order/Solver.h"',
            "logic/first_order/Solver.h": "#pragma once"}))

    def test_untyped_read_rejected(self):
        self.assertTrue(self.inspect({"search/Test.cpp": 'auto v = env::flag("XOLVER_BAD");'}))

    def test_missing_old_header_rejected(self):
        self.assertTrue(self.inspect({"ir/Test.h": '#include "expr/ir.h"\n'}))

    def test_relative_path_cannot_bypass_dependency_rules(self):
        self.assertTrue(self.inspect({"base/Test.h": '#include "../search/Solver.h"\n',
                                      "search/Solver.h": "#pragma once\n"}))

    def test_retired_expression_graph_cannot_return(self):
        self.assertTrue(self.inspect({"ir/Old.h": "class CoreIr {};\n"}))
