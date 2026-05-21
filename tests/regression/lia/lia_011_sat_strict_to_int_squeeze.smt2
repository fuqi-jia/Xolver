; In Z, x>0 and x<2 forces x=1.
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(assert (> x 0))
(assert (< x 2))
(check-sat)
