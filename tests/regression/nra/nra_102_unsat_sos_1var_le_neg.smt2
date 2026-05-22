; x² ≤ -1 is unsat (CDCAC must refute by positivity).
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (<= (* x x) (- 1)))
(check-sat)
