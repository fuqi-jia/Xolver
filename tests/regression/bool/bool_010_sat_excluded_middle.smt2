; Tautology: P or not P. Useless as a constraint, must be sat.
(set-logic QF_UF)
(set-info :status sat)
(declare-const p Bool)
(assert (or p (not p)))
(check-sat)
