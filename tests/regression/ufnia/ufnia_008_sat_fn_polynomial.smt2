; f(x) defined by polynomial constraints, sat.
(set-logic QF_UFNIA)
(set-info :status sat)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (>= x 0)) (assert (<= x 5))
(assert (= (f x) (* x x)))
(assert (>= (f x) 0))
(check-sat)
