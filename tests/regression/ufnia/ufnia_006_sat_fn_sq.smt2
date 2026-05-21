; Sat case: f(x*x) bounded but consistent.
(set-logic QF_UFNIA)
(set-info :status sat)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (>= x 0))
(assert (<= x 3))
(assert (= (f (* x x)) 7))
(check-sat)
