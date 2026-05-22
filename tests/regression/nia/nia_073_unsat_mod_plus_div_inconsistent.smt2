; mod 4 = 1, div 4 = 2 ⇒ x = 9. Then assert x = 10. Unsat.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (mod x 4) 1))
(assert (= (div x 4) 2))
(assert (= x 10))
(check-sat)
