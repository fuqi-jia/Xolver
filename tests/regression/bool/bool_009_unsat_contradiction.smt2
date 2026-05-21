; Direct contradiction: P and not P.
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert (and p (not p)))
(check-sat)
