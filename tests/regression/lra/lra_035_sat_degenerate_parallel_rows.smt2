; Two parallel equality rows pinning the same combo — degenerate basis.
; Simplex should detect redundancy without infinite pivots.

(set-info :status sat)
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ x y) 1))
(assert (= (+ (* 2 x) (* 2 y)) 2))
(check-sat)
