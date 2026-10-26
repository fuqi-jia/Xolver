# Documentation

Current interfaces and behavior:

- [Project overview, build and usage](../README.md)
- [Architecture and query flow](ARCHITECTURE.md)
- [Application interfaces](../src/applications/README.md)
- [Quantifier algorithms](../src/quantifiers/README.md)
- [Python API](../python/README.md)
- [Proof tooling and evidence boundaries](../tools/proof/README.md)
- [Server validation](../tools/remote/README.md)
- [Known-gap test contract](../tests/known_gaps/README.md)

Operational records:

- [Arithmetic validation and continuation](audit/ARITHMETIC_PERFORMANCE_HANDOFF.md)

`audit/`, `agents/`, `phase-d/`, `euf-deep/` and `preprocess-deep/` contain
revision-specific experiments, investigations and design records. Their source
hashes, measurements and unresolved issues describe the recorded revisions.
Proof research and phase plans under `proof/` are design evidence; executable
proof behavior is documented in the proof tooling reference above.

The campaign rules, NIA investigations, elimination studies and roadmaps in this
directory are research records. Their measurements and plans apply to the
revisions named in each document, rather than the current capability contract.

Current feature documentation describes the checked-out version's capabilities,
interfaces and limits. Change narratives belong in commits and pull requests;
validation provenance belongs in the run records.
