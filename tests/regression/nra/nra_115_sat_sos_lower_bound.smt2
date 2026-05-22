; Positive control: x² + y² ≥ 5 — sat (e.g. (10, 0)).
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (>= (+ (* x x) (* y y)) 5))
(check-sat)
