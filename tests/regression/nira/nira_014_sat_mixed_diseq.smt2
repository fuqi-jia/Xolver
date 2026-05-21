; distinct between (to_real i) and r — easy to satisfy.
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const i Int)
(declare-const r Real)
(assert (= i 3))
(assert (distinct (to_real i) r))
(check-sat)
