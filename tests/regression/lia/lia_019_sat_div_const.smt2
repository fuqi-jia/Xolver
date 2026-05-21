; x div 2 = 3 ⇒ x ∈ {6, 7}.
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(assert (= (div x 2) 3))
(assert (>= x 0))
(check-sat)
