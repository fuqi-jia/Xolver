(set-logic QF_UF)
(declare-const p Bool)
(assert (distinct p true))
(check-sat)
