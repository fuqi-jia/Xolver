; Modus ponens: P, P→Q, then Q should be derivable but not violated.
(set-logic QF_UF)
(set-info :status sat)
(declare-const p Bool)
(declare-const q Bool)
(assert p)
(assert (=> p q))
(assert q)
(check-sat)
