; Two unit circles + line y = x. C1∩C2 at (1/2, ±√3/2); y=x ⇒ (1/2, 1/2)?
; 1/2 ≠ √3/2 — no common point. UNSAT.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* x x) (* y y)) 1))
(assert (= (+ (* (- x 1) (- x 1)) (* y y)) 1))
(assert (= y x))
(check-sat)
