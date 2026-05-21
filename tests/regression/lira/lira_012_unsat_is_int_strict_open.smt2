; is_int conflicts with open interval (0, 1).
(set-logic QF_LIRA)
(set-info :status unsat)
(declare-const r Real)
(assert (is_int r))
(assert (> r 0))
(assert (< r 1))
(check-sat)
