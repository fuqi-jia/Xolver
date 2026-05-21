; Double negation around arith atom.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (not (not (= x 0))))
(assert (> x 0))
(check-sat)
