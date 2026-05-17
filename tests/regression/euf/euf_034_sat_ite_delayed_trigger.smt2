; Delayed trigger: cond becomes true after merge
(set-logic QF_UF)
(declare-fun c () Bool)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (= c true))
(assert (= (ite c a b) a))
(check-sat)
