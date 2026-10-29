# Partial differential equations

`pde::Solver` implements the shared differential-equation contract with multiple
coordinates and multi-index derivatives. For example, `u_x = 1`, `u_t = 2` and
`u(0,0) = 0` yield `x + 2t`. Boundary evaluation arguments and assumptions are
explicit. See the [DE contract](../README.md).
