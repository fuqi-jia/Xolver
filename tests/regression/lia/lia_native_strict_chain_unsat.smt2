(set-logic LIA)
(set-info :status unsat)
(assert (exists ((x Int)) (< 0 x 1)))
(check-sat)
