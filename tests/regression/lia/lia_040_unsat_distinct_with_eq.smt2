; x=y forced by eq + distinct asserts they differ.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (= x 7))
(assert (= y 7))
(assert (distinct x y))
(check-sat)
