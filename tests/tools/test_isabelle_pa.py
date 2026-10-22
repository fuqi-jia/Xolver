"""Boundary tests; actual theorem acceptance/rejection runs on Panda1."""
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/proof"))
SPEC = importlib.util.spec_from_file_location("xolver_isabelle_pa", ROOT / "tools/proof/isabelle_pa.py")
PA = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PA
SPEC.loader.exec_module(PA)


def query(body):
    return PA.Query(body + "\n(check-sat)")


class TranslationBoundary(unittest.TestCase):
    def test_unsupported_semantics_are_not_silently_dropped(self):
        for source in (
            "(declare-const x Real)(assert (= x x))",
            "(declare-const x Int)(assert (= (* x x) 1))",
            "(declare-const x Int)(assert (= (div x 0) 1))",
            "(declare-const x Int)(assert (= (mod 7 x) 1))",
            "(push 1)(assert false)",
            "(define-fun f ((x Int)) Int x)(assert (= (f 0) 0))",
            "(assert true)(check-sat)(assert false)",
            "(assert true)(check-sat)",
            "(declare-const x Int)(assert x)",
        ):
            with self.subTest(source=source), self.assertRaises(PA.Unsupported):
                query(source)

    def test_negative_divisors_use_nonnegative_remainder(self):
        for x, d, q, r in [(-7, -3, 3, 2), (7, -3, -2, 1), (-7, 3, -3, 2)]:
            expr = lambda n: str(n) if n >= 0 else f"(- {-n})"
            term = query("")
            div = term.term(PA.parse(f"(div {expr(x)} {expr(d)})")[0], {})
            mod = term.term(PA.parse(f"(mod {expr(x)} {expr(d)})")[0], {})
            self.assertEqual((div.constant, mod.constant), (q, r))

    def test_nary_division_is_left_associative_with_signed_divisors(self):
        for x in range(-30, 31):
            for divisors in ((2, 2), (3, -2), (-3, -2), (-3, 2, -2)):
                expr = lambda n: str(n) if n >= 0 else f"(- {-n})"
                expression = "(div " + " ".join(map(expr, (x, *divisors))) + ")"
                value = x
                for divisor in divisors:
                    value //= abs(divisor)
                    if divisor < 0:
                        value = -value
                result = query("").term(PA.parse(expression)[0], {})
                self.assertEqual(result.constant, value)
        q = query("(declare-const x Int)(assert (= (div x 2 2) 3))")
        self.assertIn("((v0 div (2 :: int)) div (2 :: int))", q.proposition("sat"))

    def test_indexed_divisibility_is_an_integer_predicate(self):
        q = query("(assert (forall ((x Int)) ((_ divisible 1000003) (* 1000003 x))))")
        self.assertIn("(1000003 :: int) dvd", q.proposition("sat"))
        for operator in ("(_ divisible 0)", "(_ divisible -3)", "(_ divisible 03)",
                         "(_ divisible x)", "(_ divisible 3 4)", "(_ unknown 3)"):
            with self.subTest(operator=operator), self.assertRaises(PA.Unsupported):
                query(f"(assert ({operator} 7))")
        with self.assertRaises(PA.Unsupported):
            query("(assert ((_ divisible 3) true))")

    def test_let_bindings_are_simultaneous(self):
        a = query("(declare-const x Int)(assert (let ((x 1) (y x)) (= y x)))")
        b = query("(declare-const x Int)(assert (= x 1))")
        self.assertEqual(a.proposition("sat"), b.proposition("sat"))

    def test_shadowing_keeps_distinct_declarations(self):
        a = query("(declare-const x Int)(assert (exists ((x Int)) "
                  "(and (exists ((x Int)) (= x 0)) (= x 1))))")
        text = a.proposition("sat")
        for name in ("v0", "v1", "v2"):
            self.assertIn(name + " :: int", text)
        self.assertIn("(v1 = (1 :: int))", text)
        self.assertIn("(v2 = (0 :: int))", text)

    def test_input_cannot_inject_isabelle_source(self):
        name = '|x"\\<close> sorry \\<open>|'
        # Backslash is prohibited by SMT-LIB quoted-symbol syntax.
        with self.assertRaises(PA.Unsupported):
            query(f"(declare-const {name} Int)(assert (= {name} 0))")
        name = '|x" sorry end (*|'
        result = query(f"(declare-const {name} Int)(assert (= {name} 0))").theory("sat")
        self.assertNotIn("sorry", result)
        self.assertNotIn("(*", result)

    def test_model_requires_every_free_symbol_and_exact_types(self):
        q = query("(declare-const x Int)(declare-const p Bool)(assert p)")
        for model in ({}, {"x": 0}, {"x": True, "p": True},
                      {"x": 0, "p": 1}, {"x": 0, "p": True, "extra": 0}):
            with self.subTest(model=model), self.assertRaises(PA.Unsupported):
                q.proposition("sat", model)
        self.assertIn("let v0", q.proposition("sat", {"x": -3, "p": True}))
        with self.assertRaises(PA.Unsupported):
            q.proposition("unsat", {"x": -3, "p": True})

    def test_malformed_syntax_is_rejected(self):
        for source in ("(", ")", '(set-info :source "unfinished)', "(assert ())",
                       "(assert (exists ((x Int) (x Int)) true))",
                       "(declare-const x Int)(declare-const |x| Int)"):
            with self.subTest(source=source), self.assertRaises(PA.Unsupported):
                query(source)


    def test_normalization_is_a_separate_proof_obligation(self):
        q = query("(assert (forall ((x Int) (y Int)) "
                  "(distinct (+ (* 3 x) (* 3 y)) 10)))")
        original = q.proposition("sat")
        theory = q.theory("sat")
        self.assertEqual(len(q.normalizations), 1)
        self.assertIn('lemma normalize_0:', theory)
        self.assertIn(f'lemma result: "{original}"', theory)
        self.assertIn("@{thms result normalize_0}", theory)
        # A corrupt hint must leave the original goal intact and emit a false
        # helper as an obligation that the proof kernel will have to reject.
        key = next(iter(q.normalizations))
        q.normalizations[key] = "False"
        corrupt = q.theory("sat")
        self.assertIn(f'lemma normalize_0: "({key}) = (False)"', corrupt)
        self.assertIn(f'lemma result: "{original}"', corrupt)

    def test_normalization_does_not_treat_piecewise_terms_as_affine(self):
        q = query("(declare-const x Int)(assert (= (abs (* 2 x)) 1))"
                  "(assert (= (div (* 2 x) 3) 1))"
                  "(assert (= (ite (< x 0) (* 2 x) (* 4 x)) 1))")
        self.assertFalse(q.normalizations)


if __name__ == "__main__":
    unittest.main()
