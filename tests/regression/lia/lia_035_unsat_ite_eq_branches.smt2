; ITE in eq context: ite(c, 1, 2) = 3 — both branches contradict.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const c Bool)
(declare-const x Int)
(assert (= x (ite c 1 2)))
(assert (= x 3))
(check-sat)
