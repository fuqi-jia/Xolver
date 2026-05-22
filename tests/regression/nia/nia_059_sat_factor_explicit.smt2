; x² - 5x + 6 = 0 ⇒ (x-2)(x-3) = 0. Solutions x ∈ {2, 3}.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (= (- (+ (* x x) 6) (* 5 x)) 0))
(check-sat)
