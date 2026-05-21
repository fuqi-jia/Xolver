; Inside unit circle + x ≥ 2 — unsat.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (< (+ (* x x) (* y y)) 1))
(assert (>= x 2))
(check-sat)
