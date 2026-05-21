; x^2 + y^2 = 1 AND y = x + 10 — disjoint, unsat. Tests CDCAC's projection
; from 2 vars to 1 (must rule out all x).
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* x x) (* y y)) 1))
(assert (= y (+ x 10)))
(check-sat)
