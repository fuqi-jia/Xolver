; Variant of nira_010 UNSOUND: three vars, mixed bound contradiction.
(set-logic QF_NIRA)
(set-info :status unsat)
(declare-const i Int)
(declare-const j Int)
(declare-const r Real)
(assert (<= i 0)) (assert (<= j 0)) (assert (<= r 0))
(assert (> (+ (to_real i) (to_real j) r) 1))
(check-sat)
