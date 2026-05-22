; 3-var, single quadratic — does mere 3-var quadratic crash?
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (= (+ (* x x) (* y y) (* z z)) 0))
(check-sat)
