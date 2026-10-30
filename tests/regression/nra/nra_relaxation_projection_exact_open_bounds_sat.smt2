(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
; The interval width is below ordinary floating-point precision at one.
(assert (> x 1))
(assert (< x (+ 1 (/ 1 115792089237316195423570985008687907853269984665640564039457584007913129639936))))
(assert (> (* x x) 1))
(check-sat)
