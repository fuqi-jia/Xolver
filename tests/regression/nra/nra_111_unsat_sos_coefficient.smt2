; 2x² + 3y² < 0 — positive coefficients, SOS with weights.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (< (+ (* 2 (* x x)) (* 3 (* y y))) 0))
(check-sat)
