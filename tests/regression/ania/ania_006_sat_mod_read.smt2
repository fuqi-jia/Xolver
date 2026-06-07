; mod-by-constant over an array read.
(set-logic QF_ANIA)
(set-info :status sat)
(declare-fun a () (Array Int Int))
(assert (= (mod (select a 0) 5) 3))
(assert (>= (select a 0) 0))
(assert (<= (select a 0) 100))
(check-sat)
