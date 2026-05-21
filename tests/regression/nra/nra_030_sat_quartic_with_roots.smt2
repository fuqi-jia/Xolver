; x^4 - 5x^2 + 4 = 0 has roots ±1, ±2. Stresses CDCAC cell construction
; across multiple disjoint cells.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (- (+ (* (* x x) (* x x)) 4) (* 5 (* x x))) 0))
(check-sat)
