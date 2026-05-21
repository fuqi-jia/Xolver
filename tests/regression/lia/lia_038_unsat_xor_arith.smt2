; xor on two arithmetic atoms — exactly one must hold, but both forced same.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (xor (>= x 5) (>= x 3)))
(assert (>= x 10))   ; both atoms true ⇒ xor false ⇒ assertion fails
(check-sat)
