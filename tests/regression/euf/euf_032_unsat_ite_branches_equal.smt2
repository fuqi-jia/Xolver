; ITE R3: a=b → distinct(ite(c,a,b), a) is unsat
(set-logic QF_UF)
(declare-fun c () Bool)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (= a b))
(assert (distinct (ite c a b) a))
(check-sat)
