; Two distinct fn applications with no shared structure — sat.
(set-logic QF_UFLIA)
(set-info :status sat)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (> (f 1) 0))
(assert (< (g 2) 0))
(check-sat)
