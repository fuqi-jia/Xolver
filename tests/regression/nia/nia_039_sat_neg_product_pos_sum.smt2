; xy = -1 ∧ x + y = 0 — sat (x=1, y=-1).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (= (* x y) (- 1)))
(assert (= (+ x y) 0))
(check-sat)
