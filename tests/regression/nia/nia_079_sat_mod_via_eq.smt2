; x = 3k + 1 form via mod: x mod 3 = 1. Force x = 7, 7 mod 3 = 1 ✓.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const k Int)
(assert (= x 7))
(assert (= (mod x 3) 1))
(check-sat)
