; x² + y² ≤ -ε is unsat.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ (* x x) (* y y)) (/ (- 1) 1000)))
(check-sat)
