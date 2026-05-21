; ite(c, false, false) is always false; asserting it true is unsat.
(set-logic QF_UF)
(set-info :status unsat)
(declare-const c Bool)
(assert (ite c false false))
(check-sat)
