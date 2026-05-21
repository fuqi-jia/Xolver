; Minimal SAT 2-CNF: (p∨q) ∧ (¬p∨q) — satisfied by q=true.
(set-logic QF_UF)
(set-info :status sat)
(declare-const p Bool)
(declare-const q Bool)
(assert (or p q))
(assert (or (not p) q))
(check-sat)
