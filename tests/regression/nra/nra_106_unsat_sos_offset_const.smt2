; (x-1)² + (y-2)² + 1 ≤ 0 — translated SOS with positive const.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ (* (- x 1) (- x 1)) (* (- y 2) (- y 2)) 1) 0))
(check-sat)
