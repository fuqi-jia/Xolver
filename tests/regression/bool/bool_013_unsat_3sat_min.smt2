; Minimal UNSAT 3-CNF: {p} ∧ {¬p∨q} ∧ {¬q}. Resolution chain.
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(declare-const q Bool)
(assert p)
(assert (or (not p) q))
(assert (not q))
(check-sat)
