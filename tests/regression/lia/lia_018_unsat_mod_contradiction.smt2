; Same number cannot have two different remainders modulo 2.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (mod x 2) 0))
(assert (= (mod x 2) 1))
(check-sat)
