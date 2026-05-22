; y = x² + 1 ∧ y ≤ 0 — unsat (parabola always ≥ 1).
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= y (+ (* x x) 1)))
(assert (<= y 0))
(check-sat)
