; ITE R1: ite(true, a, b) = a
(set-logic QF_UF)
(set-info :status sat)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (= (ite true a b) a))
(check-sat)
