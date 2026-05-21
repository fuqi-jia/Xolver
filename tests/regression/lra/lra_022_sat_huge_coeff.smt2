; Very large coefficient — rational arithmetic must not overflow / lose precision.
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(assert (> (* 1000000 x) 1))
(assert (< (* 1000000 x) 1000000))
(check-sat)
