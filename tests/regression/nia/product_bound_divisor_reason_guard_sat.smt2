; The y>=2 branch is impossible, but y=1 admits x=10. A conflict learned
; from the first branch must retain the lower bound on its divisor.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (= (* x y) 10))
(assert (>= x 6))
(assert (or (>= y 2) (= y 1)))
(check-sat)
