; Strict inequality near root: (x-1)*(x-2) > 0 has solutions outside [1,2].
; Test with x = 3 — sat.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (> (* (- x 1) (- x 2)) 0))
(assert (= x 3))
(check-sat)
