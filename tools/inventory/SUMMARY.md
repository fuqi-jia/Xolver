# Arith Solver Architecture — Phase 0 Inventory

Baseline commit: 89ba9d8 (all 15 known-fails closed, regression 577/577).

## ActiveAssignment duplication
56 references across IDL/RDL/LIRA/NIA/NIRA solvers. Identical shape:
    struct ActiveAssignment { int level; SatLit lit; TheoryAtomRecord atom; bool value; };

## Pending state
56 references. PendingConflict carries { int level; TheoryConflict conflict; } in
LIA/NIA; NRA's CdcacSolver engine additionally carries an optional CoveringCertificate
(engine-internal, NOT facade — stays in CdcacSolver).
PendingUnknown carries { int level; }.
=> Base TheoryState must track pendings BY LEVEL (clear on backtrack only when level > target).

## check() LOC (the divergence)
  NIA   337   (10-reasoner chain — biggest)
  LIA   262
  LRA   183
  NIRA  109
  IDL    73
  RDL    66
  NRA    24   (thin wrapper over CdcacSolver)
  LIRA    6   (delegates)

## Reasoner candidates
  NIA:  normalizer, validator, domains, univariate, linearDomain, squareBound,
        sumOfSquaresBound, intervalEvaluator, algebraic, bounded, localSearch  (11 fields)
  NRA:  one CdcacSolver engine
  LRA:  GeneralSimplex + LraPropagationEngine
  LIA:  GeneralSimplex + IntegerReasoner + InternalMilpEngine
