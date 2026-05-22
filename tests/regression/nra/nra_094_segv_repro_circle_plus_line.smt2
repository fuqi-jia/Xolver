; Single circle + line y = x. Drop second circle to see if minimal SEGV trigger is unit-circle×line.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* x x) (* y y)) 1))
(assert (= y x))
(check-sat)
