; AMZ: x²+y²+z² ≤ 3 ∧ x+y+z ≥ 3 — equality at (1,1,1). SAT.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (<= (+ (* x x) (* y y) (* z z)) 3))
(assert (>= (+ x y z) 3))
(check-sat)
