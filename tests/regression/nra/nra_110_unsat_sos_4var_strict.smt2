; 4-var SOS < 0.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (< (+ (* a a) (* b b) (* c c) (* d d)) 0))
(check-sat)
