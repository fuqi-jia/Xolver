; Sum of squares of non-zero things is positive: (x-1)^2 + (y-2)^2 ≤ -1 unsat.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ (* (- x 1) (- x 1)) (* (- y 2) (- y 2))) (- 1)))
(check-sat)
