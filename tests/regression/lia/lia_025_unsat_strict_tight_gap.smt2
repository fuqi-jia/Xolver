; 2 < x < 3 has no integer in Z.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (> x 2))
(assert (< x 3))
(check-sat)
