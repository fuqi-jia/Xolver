; x² + y² = -2 — equality SOS gap.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* x x) (* y y)) (- 2)))
(check-sat)
