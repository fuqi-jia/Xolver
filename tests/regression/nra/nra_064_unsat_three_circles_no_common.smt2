; Three circles intersection — all pass through origin.
; x²+y²=1, (x-1)²+y²=1, x²+(y-1)²=1 — three circles share origin only as a common pt? No.
; Pairwise: C1∩C2 at (1/2, ±√3/2); C1∩C3 at (±√3/2, 1/2).
; Common to all three: empty. So three together is UNSAT.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* x x) (* y y)) 1))
(assert (= (+ (* (- x 1) (- x 1)) (* y y)) 1))
(assert (= (+ (* x x) (* (- y 1) (- y 1))) 1))
(check-sat)
