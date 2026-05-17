; Boolean-valued function with boolean args
(set-logic QF_UF)
(declare-fun P (Bool) Bool)
(declare-fun Q (Bool) Bool)
(declare-fun a () Bool)
(assert (= a true))
(assert (P a))
(assert (Q (not a)))
(check-sat)
