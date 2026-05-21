; Variant of nira_019 UNSOUND: to_int monotonicity with strict bounds.
(set-logic QF_NIRA)
(set-info :status unsat)
(declare-const r Real)
(assert (> r 5))
(assert (< (to_int r) 5))
(check-sat)
