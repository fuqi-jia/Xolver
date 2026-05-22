; Positive control: x² + y² ≥ 0 — sat with any point (e.g. origin).
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (>= (+ (* x x) (* y y)) 0))
(check-sat)
