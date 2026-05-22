; push/pop should preserve linearization cache (or invalidate cleanly).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 1)) (assert (<= x 3))
(assert (>= y 1)) (assert (<= y 3))
(assert (>= (* x y) 1))
(push 1)
(assert (>= (* x y) 100))  ; impossible in this box, pop will discard
(pop 1)
(assert (>= (* x y) 2))
(check-sat)
