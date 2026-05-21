; Function with no constraints — sat.
(set-logic QF_UF)
(set-info :status sat)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const a U)
(check-sat)
