# Shared arithmetic search support

`search/arith` owns the common arithmetic solver base. Theory implementations
live in sibling `lia`, `lra`, `nia`, `nra`, `dl` and `mixed` directories.
Reusable search engines live in `linear`, `linearizer`, `icp`, `bitblast`,
`candidate`, `presolve` and `refute`.

Pure polynomial, interval and affine normalization code belongs to `algebra`.
PA decision procedures belong to `decision/pa`; evidence checking belongs to
`evidence`. Registering SAT atoms belongs to `search/linear`, not to affine
normalization. See [architecture decisions](../../../docs/audit/RESTRUCTURING.md)
and the enforced source ownership in `src/sources.cmake`.
