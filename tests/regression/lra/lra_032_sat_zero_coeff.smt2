; Zero coefficient — degenerate equation reduces to 0 = 0.
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* 0 x) (* 0 y)) 0))
(check-sat)
