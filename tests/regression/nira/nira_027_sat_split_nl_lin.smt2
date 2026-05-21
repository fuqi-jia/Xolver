; Mix of nonlinear and linear atoms — atomizer must route each appropriately.
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const r Real)
(declare-const i Int)
(assert (>= (* r r) 1))   ; nonlinear-real
(assert (<= i 5))         ; pure-linear-int
(assert (<= r 10))        ; pure-linear-real
(check-sat)
