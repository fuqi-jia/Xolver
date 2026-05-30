; Regression for the SOMTParser DT-name-clobber bug (fixed in
; fix/dt-preserve-name-in-let-substitution at SOMTParser branch fb7fae6).
; When a let-bound subexpression contains a tester ((_ is C) x) and the
; let-substitution rebuilds the node, mkOper used to re-stamp the tester's
; name with kindToString(NT_DT_TESTER) = "UNKNOWN_KIND". Downstream the EUF
; symbol becomes "#dt.is.UNKNOWN_KIND" and DtReasoner's tester-consistency
; check false-conflicts is-empty(x) AND x=empty. Pre-fix: this case
; returned unsat (false-UNSAT). Post-fix: sat.
(set-info :status sat)
(set-logic QF_DT)
(declare-datatypes ((Enum 0)) (((A) (B))))
(declare-datatypes ((Tower 0)) (((stack (top Enum) (rest Tower)) (empty))))
(declare-fun x () Tower)
(declare-fun y () Tower)
(assert (= y empty))
; The let-bound subexpression embeds a tester; SOMTParser's let
; substitution path used to lose the tester's name here.
(assert (let ((?v (= x y)))
          (and ?v ((_ is empty) x))))
(check-sat)
