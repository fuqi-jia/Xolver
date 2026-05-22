; mod(x, 3) = mod(y, 3) with x=7, y=8 — 7 mod 3 = 1, 8 mod 3 = 2 ⇒ unsat.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (= x 7))
(assert (= y 8))
(assert (= (mod x 3) (mod y 3)))
(check-sat)
