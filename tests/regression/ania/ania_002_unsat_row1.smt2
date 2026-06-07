; Read-over-write same index must equal the stored value: negation is unsat.
(set-logic QF_ANIA)
(set-info :status unsat)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun v () Int)
(assert (not (= (select (store a i v) i) v)))
(check-sat)
