; x² - 4 = 0 AND x² - 9 = 0 — {-2,2} ∩ {-3,3} = ∅. UNSAT.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (- (* x x) 4) 0))
(assert (= (- (* x x) 9) 0))
(check-sat)
