; Minimal UNSAT 2-CNF: (p) ∧ (¬p).
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
