; Product of two distinct-index reads equals 12.
(set-logic QF_ANIA)
(set-info :status sat)
(declare-fun a () (Array Int Int))
(assert (= (* (select a 0) (select a 1)) 12))
(assert (> (select a 0) 0))
(assert (> (select a 1) 0))
(check-sat)
