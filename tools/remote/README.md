# Server validation

`validate.sh <label> [source-overlay.tar.gz]` configures and builds the checkout's
single `build/` directory under an exclusive writer lock. It freezes binaries,
test inputs and hashes into `validation/<label>/`, then releases the lock before
running the immutable test snapshot. Results do not contain a duplicate build
tree. Run the driver through the server scheduler (ExperimentOS).

`package_overlay.py` and `apply_overlay.py` transfer changed source files with
content hashes and checked deletions. `freeze_validation.py` captures test inputs
and their provenance. `validate_gate.sh` supports paired source-control cleanup
validation against an explicitly named reference binary.

Server dependency locations are parameters of the validation drivers. Configure
them for the target checkout. Use bounded build/test parallelism, inspect host
resources before large runs, and retain original benchmark archives in their
shared immutable storage location.
