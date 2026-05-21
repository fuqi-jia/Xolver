; distinct on 3 booleans is unsat — only 2 values available.
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (distinct p q r))
(check-sat)
