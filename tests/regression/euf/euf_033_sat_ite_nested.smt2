; Nested ITE
(set-logic QF_UF)
(declare-fun c1 () Bool)
(declare-fun c2 () Bool)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (= (ite c1 (ite c2 a b) b) b))
(check-sat)
