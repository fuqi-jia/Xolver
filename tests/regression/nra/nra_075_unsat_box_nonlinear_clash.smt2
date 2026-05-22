; Same box + x² + y² > 4 — impossible (max x²+y² = 2).
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0)) (assert (<= x 1))
(assert (>= y 0)) (assert (<= y 1))
(assert (> (+ (* x x) (* y y)) 4))
(check-sat)
