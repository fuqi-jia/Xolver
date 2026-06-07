; Pair datatype: selector over constructor, with a nonlinear field constraint.
(set-logic QF_UFDTNIA)
(set-info :status sat)
(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))
(declare-fun p () Pair)
(assert (= (* (fst p) (fst p)) 16))
(assert (>= (fst p) 0))
(assert (= (snd p) 7))
(check-sat)
