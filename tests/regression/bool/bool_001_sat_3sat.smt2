(set-info :status sat)

(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (or p q r))
(assert (or (not p) (not q)))
(assert (or (not q) (not r)))
(check-sat)
