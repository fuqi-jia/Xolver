; SEGV minimization from nra_040. Drop the half-space `x ≥ 9/10`.
; Pure sphere only.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (= (+ (* x x) (* y y) (* z z)) 1))
(check-sat)
