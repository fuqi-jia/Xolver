; x*y = 6 with x,y ≥ 1 — finitely many factorizations.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (= (* x y) 6))
(assert (>= x 1))
(assert (>= y 1))
(check-sat)
