; 3-var quadric with neg constant: x² + y² + z² = -1 — unsat.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (= (+ (* x x) (* y y) (* z z)) (- 1)))
(check-sat)
