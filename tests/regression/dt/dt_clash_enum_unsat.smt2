; Constructor clash on an enum datatype: x = red and x = green forces
; red = green, but distinct constructors are disjoint -> unsat.
(set-info :status unsat)
(set-logic QF_UFDT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-const x Color)
(assert (= x red))
(assert (= x green))
(check-sat)
