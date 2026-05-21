; Sat: f(x) inside polynomial constraint, witness exists.
(set-logic QF_UFNRA)
(set-info :status sat)
(declare-fun f (Real) Real)
(declare-const x Real)
(assert (= (+ (* x x) 1) (f x)))
(assert (>= x 0))
(assert (<= x 1))
(check-sat)
