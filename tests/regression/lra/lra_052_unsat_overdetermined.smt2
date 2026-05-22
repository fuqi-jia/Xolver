; Overdetermined LRA: 5 equations on 3 vars, last conflicts.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real) (declare-const y Real) (declare-const z Real)
(assert (= (+ x y z) 6))
(assert (= (+ x (* 2 y) (* 3 z)) 14))
(assert (= (+ (* 2 x) (* 3 y) (* 5 z)) 23))
(assert (= (+ x y) 3))   ; z = 3
(assert (= y 3))          ; then x = 0; check: 0+3+3=6 OK, 0+6+9=15 ≠14 — UNSAT.
(check-sat)
