; x^5 = 32 has unique real root x = 2. Quintic — exercises algebraic-number
; representation in CDCAC.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (* x (* x (* x (* x x)))) 32))
(check-sat)
