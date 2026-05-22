; (x² + y²) < 0 — strict, 2 vars.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (< (+ (* x x) (* y y)) 0))
(check-sat)
