; xor p q and p = q is unsat.
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(declare-const q Bool)
(assert (xor p q))
(assert (= p q))
(check-sat)
