; Predicate transitivity
(set-logic QF_UF)
(declare-fun P (Int) Bool)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= a b))
(assert (P a))
(assert (not (P b)))
(check-sat)
