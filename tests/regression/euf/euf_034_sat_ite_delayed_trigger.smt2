; Delayed trigger: cond becomes true after merge
(set-logic QF_UF)
(set-info :status sat)
(declare-fun c () Bool)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (= c true))
(assert (= (ite c a b) a))
(check-sat)
