; Variant of lira_012 UNSOUND: is_int with eq to non-integer rational.
(set-logic QF_LIRA)
(set-info :status unsat)
(declare-const r Real)
(assert (is_int r))
(assert (= r (/ 1 2)))
(check-sat)
