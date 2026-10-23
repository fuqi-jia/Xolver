# UNSAT proof corpus

`UNSAT-CORPUS.txt` lists the proof-checking inputs. `select_corpus.sh` selects
the two smallest files by line count in each regression directory, restricted to
`:status unsat` and excluding cases marked `known-fail` or `known-unsound`.

```bash
bash docs/proof/corpus/select_corpus.sh > docs/proof/corpus/UNSAT-CORPUS.txt
```

The corpus is distinct from the full regression suite. A listed UNSAT case may
have a complete emitted proof, a Boolean skeleton or no certificate. See the
[proof checker contract](../../../tools/proof/README.md) for result meanings.
Coverage counts belong to validation records for the exact tested revision.
