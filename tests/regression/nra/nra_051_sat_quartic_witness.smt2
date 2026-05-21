; x^4 = 16 has roots ±2 — must find one.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (* (* x x) (* x x)) 16))
(assert (> x 0))
(check-sat)
