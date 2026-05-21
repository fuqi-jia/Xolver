; High-degree polynomial with small rational coefficients — root isolation stress.
; p(x) = x^5 - 5x^3 + 4x ≥ 0 has root structure {-2, -1, 0, 1, 2}.
; Take x=3 in the always-positive tail.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= x 3))
(assert (>= (+ (* x (* x (* x (* x x)))) (* 4 x)) (* 5 (* x (* x x)))))
(check-sat)
