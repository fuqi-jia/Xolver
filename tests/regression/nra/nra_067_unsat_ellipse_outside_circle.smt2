; Ellipse x²/4 + y² = 1 (largest |x| = 2) AND x ≥ 3 — empty.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (/ (* x x) 4) (* y y)) 1))
(assert (>= x 3))
(check-sat)
