; Tight interval around x=1: (x-1)^2 ≤ 1/10000 means x is close to 1.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (<= (* (- x 1) (- x 1)) (/ 1 10000)))
(check-sat)
