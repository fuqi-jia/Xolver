; p = (x-1)(x²+1), q = (x-1)(x+2). gcd = (x-1). Both zero ⇒ x=1.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (* (- x 1) (+ (* x x) 1)) 0))
(assert (= (* (- x 1) (+ x 2)) 0))
(check-sat)
