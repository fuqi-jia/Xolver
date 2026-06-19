; #81 — a self-difference (- x x) is a CONSTANT constraint 0 (rel) c. Here
; (> (- x x) 14) is 0 > 14 = false, so the conjunction is unsat. Before the fix
; the RDL normalizer treated the zero-term LHS as "unsupported" and floored the
; ENTIRE check to unknown (these atoms are ubiquitous in temporal-planning
; encodings, e.g. QF_RDL/SMT-Temporal-Planning-Benchmarks/cooking*). Now the
; constant is evaluated directly -> a one-literal ImmediateConflict.
(set-logic QF_RDL)
(set-info :status unsat)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (>= (- x y) 3))
(assert (> (- x x) 14))
(check-sat)
