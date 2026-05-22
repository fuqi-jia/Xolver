; Two polynomials sharing common factor:
; (x-1)(x-2) = 0 AND (x-1)(x-3) = 0 — share x=1.
; But add x=5 — unsat. Tests SubresultantEngine common factor detection.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (= (* (- x 1) (- x 2)) 0))
(assert (= (* (- x 1) (- x 3)) 0))
(assert (= x 5))
(check-sat)
