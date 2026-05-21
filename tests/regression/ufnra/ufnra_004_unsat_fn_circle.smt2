; UFNRA: fn used inside circle constraint, then contradicted.
(set-logic QF_UFNRA)
(set-info :status unsat)
(declare-fun f (Real) Real)
(declare-const x Real)
(assert (= (+ (* x x) (* (f x) (f x))) 1))
(assert (>= x 2))
(check-sat)
