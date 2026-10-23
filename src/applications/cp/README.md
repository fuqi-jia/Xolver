# Constraint programming

`Problem` accepts native constraints, unrestricted/enumerated/interval variable
domains, and all-different groups. `Solver` compiles domain membership and global
constraints into native formulas and passes an independent query snapshot to an
injected `DecisionOracle`. Empty finite domains are inconsistent.

Domain declarations are problem semantics. The interface does not require a
particular propagation or search strategy. Oracle results retain their model or
unknown reason. Additional global propagators can implement the same contract.
