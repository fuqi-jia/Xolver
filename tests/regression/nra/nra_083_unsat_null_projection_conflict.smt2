; y*(x-1) = 0 AND y > 0 forces x = 1; assert x = 2 ⇒ unsat.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= (* y (- x 1)) 0))
(assert (> y 0))
(assert (= x 2))
(check-sat)
