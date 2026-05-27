; Satisfiable enum choice: x is red or green (x != blue). The chosen constructor
; determines x's class, so Zolver returns a sound sat.
(set-info :status sat)
(set-logic QF_UFDT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-const x Color)
(assert (or (= x red) (= x green)))
(assert (not (= x blue)))
(check-sat)
