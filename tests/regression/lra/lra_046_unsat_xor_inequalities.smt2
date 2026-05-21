; xor on two real ineqs, both forced true.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(assert (xor (> x 0) (>= x 0)))
(assert (= x 1))   ; both atoms true ⇒ xor false ⇒ unsat
(check-sat)
