; 3-variable quadric: x² + 2y² + 3z² = 6. Witness (1,1,1).
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (= (+ (* x x) (* 2 (* y y)) (* 3 (* z z))) 6))
(check-sat)
