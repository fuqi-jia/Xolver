; xor of two — exactly one true.
(set-logic QF_UF)
(set-info :status sat)
(declare-const p Bool)
(declare-const q Bool)
(assert (xor p q))
(check-sat)
