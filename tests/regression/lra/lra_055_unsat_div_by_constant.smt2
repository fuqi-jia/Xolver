; Division by a constant, unsat: (x+y)/3 <= 4 (=> x+y <= 12) and x/2 >= 10
; (=> x >= 20) with y = 0 forces x <= 12 and x >= 20. Contradiction.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (/ (+ x y) 3) 4))
(assert (>= (/ x 2) 10))
(assert (= y 0))
(check-sat)
