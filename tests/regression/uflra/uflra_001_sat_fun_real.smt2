; Function result in real arithmetic
(set-logic QF_UFLRA)
(set-info :status sat)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x y))
(assert (= (+ (f x) (f y)) 1.5))
(check-sat)
