; Pure LRA under LIRA logic — atomizer should route to LRA.
(set-logic QF_LIRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ x y) 1))
(assert (>= x 0))
(assert (<= y 1))
(check-sat)
