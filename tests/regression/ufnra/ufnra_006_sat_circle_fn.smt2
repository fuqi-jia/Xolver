; f mapping to circle: f(x)² + x² = 1, sat with x=0, f(0)=1.
(set-logic QF_UFNRA)
(set-info :status sat)
(declare-fun f (Real) Real)
(declare-const x Real)
(assert (= (+ (* x x) (* (f x) (f x))) 1))
(assert (= x 0))
(check-sat)
