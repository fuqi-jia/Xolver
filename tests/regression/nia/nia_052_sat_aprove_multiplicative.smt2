; AProVE-style: (x+1)*(y+1) ≥ 1 with x,y ≥ 0 — sat (always when both ≥ 0).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0))
(assert (>= y 0))
(assert (>= (* (+ x 1) (+ y 1)) 1))
(check-sat)
