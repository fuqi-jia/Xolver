; Variant: is_int in negative open interval.
(set-logic QF_LIRA)
(set-info :status unsat)
(declare-const r Real)
(assert (is_int r))
(assert (> r (- 1)))
(assert (< r 0))
(check-sat)
