; Function result used in linear arithmetic
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(assert (= (+ (f x) (f y)) 10))
(check-sat)
