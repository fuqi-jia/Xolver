; ITE R1: ite(true, a, b) = a
(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (= (ite true a b) a))
(check-sat)
