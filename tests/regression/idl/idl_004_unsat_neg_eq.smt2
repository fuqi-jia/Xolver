; Negated equality via difference: ¬(x - y = 0) plus chain forcing x=y.
(set-logic QF_IDL)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (<= (- x y) 0))
(assert (<= (- y x) 0))
(assert (not (= (- x y) 0)))
(check-sat)
