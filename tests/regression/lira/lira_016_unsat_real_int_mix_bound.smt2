; Real r squeezed by int bounds and forced equal to non-integer.
(set-logic QF_LIRA)
(set-info :status unsat)
(declare-const r Real)
(declare-const i Int)
(assert (= r (/ 3 2)))
(assert (= (to_real i) r))
(check-sat)
