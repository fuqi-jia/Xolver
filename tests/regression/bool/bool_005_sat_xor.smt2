(set-info :status sat)

(declare-const p Bool)
(declare-const q Bool)
(assert (xor p q))
(assert p)
(check-sat)
