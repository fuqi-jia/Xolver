; 2x + 3y = 5 AND 5x + 7y = 11. Gauss: y=3, x=-2. Negative, but allowed.
; Add x ≥ 0, then both forces give y=3, x=-2 — contradicts x ≥ 0. UNSAT.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 2 x) (* 3 y)) 5))
(assert (= (+ (* 5 x) (* 7 y)) 11))
(assert (>= x 0))
(check-sat)
