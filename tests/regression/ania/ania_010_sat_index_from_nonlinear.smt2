; A computed (nonlinear) index used to read; consistent value.
(set-logic QF_ANIA)
(set-info :status sat)
(declare-fun a () (Array Int Int))
(declare-fun k () Int)
(assert (= (* k k) 4))
(assert (= k 2))
(assert (= (select a (* k k)) 7))
(check-sat)
