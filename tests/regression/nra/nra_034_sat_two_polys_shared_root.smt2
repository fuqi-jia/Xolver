; (x-1)(x-2) = 0 AND (x-2)(x-3) = 0 share root x = 2.
; Tests CDCAC's ability to find shared cell.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (* (- x 1) (- x 2)) 0))
(assert (= (* (- x 2) (- x 3)) 0))
(check-sat)
