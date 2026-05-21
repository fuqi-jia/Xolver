; Sphere x²+y²+z² = 1 with x ≥ 0.9 — exists, e.g. (0.95, 0, 0).
; Stresses 3-variable CDCAC.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (= (+ (* x x) (* y y) (* z z)) 1))
(assert (>= x (/ 9 10)))
(check-sat)
