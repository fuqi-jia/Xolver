; (1/3) x + (2/3) y = 1, x = 0, y = 0 — unsat.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* (/ 1 3) x) (* (/ 2 3) y)) 1))
(assert (= x 0))
(assert (= y 0))
(check-sat)
