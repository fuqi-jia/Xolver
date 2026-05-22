; Three quadrics, pairwise disjoint witness sets — no triple intersection.
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (= (+ (* x x) (* y y) (* z z)) 1))         ; unit sphere
(assert (= (+ (* (- x 3) (- x 3)) (* y y) (* z z)) 1)) ; sphere centered (3,0,0)
(assert (= (+ (* x x) (* (- y 5) (- y 5)) (* z z)) 1)) ; sphere centered (0,5,0)
(check-sat)
