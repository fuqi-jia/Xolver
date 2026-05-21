; VeryMax-style: rank function 2x + y is > 0 at (x=1, y=0) — sat.
; If GCD conflict on (2x+y) > 0 ∧ x ≥ 1 fires wrongly, returns unsat.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 1))
(assert (>= y 0))
(assert (> (+ (* 2 x) y) 0))
(check-sat)
