; Binary fn congruence + arithmetic equality.
(set-logic QF_UFLIA)
(set-info :status unsat)
(declare-fun h (Int Int) Int)
(declare-const a Int) (declare-const b Int)
(assert (= a b))
(assert (distinct (h a 1) (h b 1)))
(check-sat)
