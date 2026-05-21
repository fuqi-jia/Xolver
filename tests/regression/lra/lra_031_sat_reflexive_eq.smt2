; Reflexive equality is a tautology.
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(assert (= x x))
(check-sat)
