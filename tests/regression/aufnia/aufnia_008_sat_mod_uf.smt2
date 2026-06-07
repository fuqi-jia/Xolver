; mod-by-constant of a UF image over an array read.
(set-logic QF_AUFNIA)
(set-info :status sat)
(declare-fun a () (Array Int Int))
(declare-fun f (Int) Int)
(assert (= (mod (f (select a 0)) 7) 4))
(assert (>= (f (select a 0)) 0))
(assert (<= (f (select a 0)) 50))
(check-sat)
