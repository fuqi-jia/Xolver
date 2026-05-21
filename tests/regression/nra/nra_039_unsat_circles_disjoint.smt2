; Two disjoint circles: x²+y² ≤ 1 centered at origin, (x-5)²+y² ≤ 1 centered at (5,0).
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ (* x x) (* y y)) 1))
(assert (<= (+ (* (- x 5) (- x 5)) (* y y)) 1))
(check-sat)
