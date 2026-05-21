; Pure-integer constraint under NIRA logic.
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const i Int)
(assert (>= i 0))
(assert (<= i 5))
(assert (= (mod i 2) 1))
(check-sat)
