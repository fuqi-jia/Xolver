# Modular graded-ladder validation (flag-ON, NOT default ctest)

Isolated small-k always-true-mod-k instances of the oracle-blind modular-UNSAT
pattern. Run with XOLVER_NIA_MODULAR=1 and cross-check vs z3:

  for f in *.smt2; do z3 -smt2 $f; XOLVER_NIA_MODULAR=1 xolver solve $f; done

All are UNSAT (:status unsat, python-verified). Validation result (2026-05-29):
- z3 DECIDES L1 (x^2 mod4=2), L3 (x^2+x mod2=1), L5 (2x^2 mod4=3) -> all unsat,
  AGREES with our engine -> engine's mod-k reasoning validated on z3-checkable cases.
- z3 CANNOT decide L2 (x^2 mod3=2) or L4 (isolated ps4 goal mod4) -- the oracle-blind
  regime. Our engine returns unsat with brute-force cert = ConfirmedUnsat (independent),
  python-confirmed. The real oracle-blind cases (ps/STC) use the SAME code path =>
  inherit this confidence.

These are flag-ON cases (default-OFF engine returns unknown), so they live here, not
in tests/regression/ (which must stay green at default).
