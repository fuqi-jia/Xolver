; Quadratic constraint with explicit witness: x² - 2x + 1 = 0 has x = 1.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (= (- (+ (* x x) 1) (* 2 x)) 0))
(check-sat)
