(set-logic QF_LRA)
(set-info :status sat)
; ITE over integer-literal branches in a Real formula -> ITE lowering creates a
; synthetic Int-sorted aux ("__nlc_ite_*"). LogicFeatureDetector must SKIP that
; synthetic Int var, else QF_LRA is wrongly flagged Mixed -> Unknown. Locks the
; gasburner merge-casualty regression.
(declare-fun b () Bool)
(declare-fun x () Real)
(assert (< (ite b 0 1) x))
(assert (< x 5))
(check-sat)
