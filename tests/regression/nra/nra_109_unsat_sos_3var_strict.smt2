; x² + y² + z² < 0 — 3 vars (companion to existing nra_073).
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (< (+ (* x x) (* y y) (* z z)) 0))
(check-sat)
