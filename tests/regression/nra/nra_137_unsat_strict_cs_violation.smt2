; Cauchy-Schwarz strict violation: 4·(x²+y²+z²) < (x+y+z)² requires equality. Always false.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (< (* 4 (+ (* x x) (* y y) (* z z))) (* (+ x y z) (+ x y z))))
(check-sat)
