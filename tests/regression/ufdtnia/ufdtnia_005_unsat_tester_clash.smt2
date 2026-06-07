; A value cannot be two distinct constructors at once.
(set-logic QF_UFDTNIA)
(set-info :status unsat)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-fun c () Color)
(assert ((_ is red) c))
(assert ((_ is green) c))
(check-sat)
