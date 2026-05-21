; is_int holds for integral real value.
(set-logic QF_LIRA)
(set-info :status sat)
(declare-const r Real)
(assert (is_int r))
(assert (>= r 0))
(assert (<= r 10))
(check-sat)
