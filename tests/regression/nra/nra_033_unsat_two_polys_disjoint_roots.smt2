; (x-1)(x-2) = 0 AND (x-3)(x-4) = 0 — disjoint root sets ⇒ unsat.
; Stresses CDCAC variable elimination across multiple polynomials.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (= (* (- x 1) (- x 2)) 0))
(assert (= (* (- x 3) (- x 4)) 0))
(check-sat)
