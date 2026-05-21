; distinct on 2 booleans is satisfiable: one true, one false.
(set-logic QF_UF)
(set-info :status sat)
(declare-const p Bool)
(declare-const q Bool)
(assert (distinct p q))
(check-sat)
