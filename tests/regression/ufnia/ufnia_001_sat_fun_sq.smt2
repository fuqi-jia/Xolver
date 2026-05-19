; Function result in nonlinear integer arithmetic
(set-logic QF_UFNIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (= (* (f x) (f x)) 16))
(assert (>= (f x) 0))
(check-sat)
