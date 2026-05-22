; Classic AMZ-class: x² + y² + z² ≤ a ∧ x+y+z ≥ b ∧ b² > 3a is empty
; (Cauchy-Schwarz: (x+y+z)² ≤ 3(x²+y²+z²) ≤ 3a < b²).
; With a=1, b=2: 4 > 3 OK, so unsat.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (<= (+ (* x x) (* y y) (* z z)) 1))
(assert (>= (+ x y z) 2))
(check-sat)
