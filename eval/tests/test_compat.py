"""Tests for eval._compat — the Python 3.6 dataclass fallback shim.

These exercise the FALLBACK implementation directly (so the 3.6 code path is
validated even when running on 3.7+). Python 3.6+ / stdlib unittest.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval._compat import fallback_dataclass, fallback_field  # noqa: E402


class TestFallbackDataclass(unittest.TestCase):
    def test_init_positional_and_defaults(self):
        @fallback_dataclass
        class P:
            a: int
            b: int = 5
        p = P(1)
        self.assertEqual((p.a, p.b), (1, 5))
        self.assertEqual(P(1, 2).b, 2)

    def test_init_keyword_args(self):
        @fallback_dataclass
        class P:
            a: int
            b: int = 5
        p = P(a=3, b=7)
        self.assertEqual((p.a, p.b), (3, 7))

    def test_default_factory_gives_independent_instances(self):
        @fallback_dataclass
        class P:
            items: list = fallback_field(default_factory=list)
        x, y = P(), P()
        x.items.append(1)
        self.assertEqual(y.items, [])  # not shared across instances

    def test_eq_and_repr(self):
        @fallback_dataclass
        class P:
            a: int
            b: int = 0
        self.assertEqual(P(1, 2), P(1, 2))
        self.assertNotEqual(P(1, 2), P(1, 3))
        self.assertEqual(repr(P(1, 2)), "P(a=1, b=2)")

    def test_missing_required_raises(self):
        @fallback_dataclass
        class P:
            a: int
        with self.assertRaises(TypeError):
            P()

    def test_unexpected_kwarg_raises(self):
        @fallback_dataclass
        class P:
            a: int
        with self.assertRaises(TypeError):
            P(1, nope=2)


class TestCompatExports(unittest.TestCase):
    def test_module_exports_dataclass_and_field(self):
        from eval import _compat
        self.assertTrue(hasattr(_compat, "dataclass"))
        self.assertTrue(hasattr(_compat, "field"))


if __name__ == "__main__":
    unittest.main()
