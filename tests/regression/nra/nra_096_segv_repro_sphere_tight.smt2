; Sphere + tight equality on one var — collapses to 2-var circle.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (= (+ (* x x) (* y y) (* z z)) 1))
(assert (= z 0))
(check-sat)
