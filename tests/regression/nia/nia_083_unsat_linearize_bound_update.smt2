; Tight bounds with x*y bound conflict.
; x ∈ [1,2], y ∈ [1,2] ⇒ x*y ∈ [1,4]. Asserting x*y > 10 ⇒ unsat.
; McCormick must produce the upper-bound cut x*y ≤ 4.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 1)) (assert (<= x 2))
(assert (>= y 1)) (assert (<= y 2))
(assert (> (* x y) 10))
(check-sat)
