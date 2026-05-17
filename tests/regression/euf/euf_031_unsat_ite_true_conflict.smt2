; ITE R1 conflict: distinct(ite(c,a,b), a) ∧ c=true
(set-logic QF_UF)
(declare-fun c () Bool)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (= c true))
(assert (distinct (ite c a b) a))
(check-sat)
