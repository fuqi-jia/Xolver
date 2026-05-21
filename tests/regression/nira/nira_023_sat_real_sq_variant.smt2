; Variant of nira_009 UNSOUND: integer with nonlinear-real, different constant.
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const i Int)
(declare-const r Real)
(assert (= i 5))
(assert (> r 0))
(assert (= (* r r) 5))
(check-sat)
