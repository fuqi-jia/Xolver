; Small-prime-modular SAT control: same shape as nia_116 but x*x-y=2 ⟹ 2*x^2=2 ⟹
; x^2=1, so x=1, y=-1 is a model. Guards against the modular stage over-claiming —
; a wrong GF(p) check here would be a false unsat. z3-confirmed sat.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* x x) y) 0))
(assert (= (- (* x x) y) 2))
(check-sat)
