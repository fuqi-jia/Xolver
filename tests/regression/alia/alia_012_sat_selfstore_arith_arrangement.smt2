; Integer analog of the arrangement-splitting residual; sat (i0!=i1).
(set-logic QF_ALIA)
(set-info :status sat)
(declare-const a (Array Int Int))
(declare-const i0 Int)(declare-const i1 Int)(declare-const e0 Int)(declare-const e1 Int)
(assert (= a (store a i0 e0)))
(assert (= a (store a i1 e1)))
(assert (= e1 (+ e0 3)))
(check-sat)
