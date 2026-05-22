; Same circle but assert x = 2 ⇒ x² ≥ 4, but f(x)² + x² = 1 implies x² ≤ 1. Unsat.
(set-logic QF_UFNRA)
(set-info :status unsat)
(declare-fun f (Real) Real)
(declare-const x Real)
(assert (= (+ (* x x) (* (f x) (f x))) 1))
(assert (= x 2))
(check-sat)
