; Variant of uflia_003: bridge bug with negative-coefficient bounds.
(set-logic QF_UFLIA)
(set-info :status unsat)
(declare-fun g (Int) Int)
(declare-fun y () Int)
(assert (= y (- 3)))
(assert (< (g y) 0))
(assert (> (g (- 3)) 5))
(check-sat)
