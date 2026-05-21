; Integer i must be ≥ 0 and (to_real i) < 0.5 forces i = 0.
; Add i > 0 to make unsat.
(set-logic QF_LIRA)
(set-info :status unsat)
(declare-const i Int)
(assert (>= i 0))
(assert (< (to_real i) (/ 1 2)))
(assert (> i 0))
(check-sat)
