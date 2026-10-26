from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.qcp_proof_promotion import promote_auto_text, token_mask


class QcpProofPromotionTests(unittest.TestCase):
    def test_all_admitted_auto_witnesses_remain_required_manual_proofs(self):
        auto = 'Require Import Goal.\nLemma p1 : g1. Proof. Admitted.\nLemma p2 : g2. Proof. Admitted.\n'
        manual = 'Require Import Goal Auto.\nLemma p3 : g3. Proof. Admitted.\n'
        a, m, moved = promote_auto_text(auto, manual)
        self.assertNotIn('Admitted', a)
        self.assertEqual([x['goal'] for x in moved], ['g1', 'g2'])
        self.assertEqual(m.count('Admitted'), 3)
        self.assertLess(m.index('Lemma p1'), m.index('Lemma p3'))
        self.assertEqual(promote_auto_text(a, m), (a, m, []))

    def test_preserves_completed_independent_auto_proofs(self):
        auto = 'Lemma p : g. Proof. Admitted.\nLemma independent : True. Proof. exact I. Qed.\n'
        a, m, _ = promote_auto_text(auto, '')
        self.assertIn('exact I. Qed.', a)
        self.assertIn('Lemma p', m)

    def test_comments_strings_and_nested_comments_cannot_forge_witnesses(self):
        source = '(* Lemma fake : fake. Proof. Admitted. (* nested *) *)\nDefinition text := "Admitted. ""Lemma""".\n'
        a, m, moved = promote_auto_text(source, '')
        self.assertEqual(a, source)
        self.assertEqual(m, '')
        self.assertFalse(moved)
        self.assertEqual(len(token_mask(source)), len(source))

    def test_rejects_unchecked_assumptions_complex_stubs_and_overlap(self):
        for auto, manual in [
                ('Axiom p : True.', ''),
                ('Lemma p : forall x, x=x. Proof. Admitted.', ''),
                ('Lemma p : g. Proof. Admitted.', 'Lemma p : g. Proof. Abort.'),
                ('Lemma p : g. Proof. Admitted. Lemma p : g. Proof. Admitted.', ''),
                ('Lemma p : g. Proof. Admitted. Lemma q : g. Proof. exact p. Qed.', '')]:
            with self.subTest(auto=auto), self.assertRaises(ValueError):
                promote_auto_text(auto, manual)


if __name__ == '__main__':
    unittest.main()
