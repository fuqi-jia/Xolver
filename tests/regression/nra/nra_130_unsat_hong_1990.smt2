; Hong 1990 example: classic CAD benchmark.
; ∃x,y. x² + y² ≤ 1 ∧ x² - y² ≥ 1 ∧ x ≥ 0 ∧ y > 0
; From first two: 2x² ≥ 2, so x² ≥ 1, x ≥ 1. But x² + y² ≤ 1 ⇒ x² ≤ 1 - y² < 1 ⇒ x < 1. Contradiction.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ (* x x) (* y y)) 1))
(assert (>= (- (* x x) (* y y)) 1))
(assert (>= x 0))
(assert (> y 0))
(check-sat)
