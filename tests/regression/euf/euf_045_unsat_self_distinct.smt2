; distinct of a term with itself is trivially unsat (any term equals itself).
(set-logic QF_UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-const a U)
(assert (distinct a a))
(check-sat)
