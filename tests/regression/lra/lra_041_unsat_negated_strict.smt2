; Negated strict + positive — LRA false-sat repro.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(assert (not (> x 0)))
(assert (> x 0))
(check-sat)
