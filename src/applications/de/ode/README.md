# Ordinary differential equations

`ode::Solver` implements the shared differential-equation contract for one real
coordinate. Native equations, derivative declarations and initial conditions
are supplied explicitly. For example, `y' = 2` and `y(0) = 1` yield `1 + 2t`.
Returned functions are checked against the equations. See the [DE contract](../README.md).
