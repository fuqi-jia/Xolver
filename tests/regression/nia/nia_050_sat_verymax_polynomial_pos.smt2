; Polynomial expression > 0 with explicit witness — VeryMax style.
; (x-y)² + 1 > 0 — always sat (trivially).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (> (+ (* (- x y) (- x y)) 1) 0))
(check-sat)
