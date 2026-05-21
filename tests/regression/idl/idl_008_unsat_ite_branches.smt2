; ITE selecting between two difference atoms, both contradict outer constraint.
(set-logic QF_IDL)
(set-info :status unsat)
(declare-const c Bool)
(declare-const x Int)
(declare-const y Int)
(assert (ite c (<= (- x y) (- 10)) (<= (- x y) (- 5))))
(assert (>= (- x y) 0))
(check-sat)
