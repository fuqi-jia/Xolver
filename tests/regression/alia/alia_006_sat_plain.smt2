(set-logic QF_ALIA)
(set-info :status sat)
; genuinely satisfiable: a stored value read back equals 5, index constrained
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (= (select (store a i 5) i) 5))
(assert (> i 0))
(assert (< i 10))
(check-sat)
