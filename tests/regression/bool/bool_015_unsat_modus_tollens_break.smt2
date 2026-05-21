; Modus tollens broken: assert P, P→Q, and ¬Q.
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(declare-const q Bool)
(assert p)
(assert (=> p q))
(assert (not q))
(check-sat)
