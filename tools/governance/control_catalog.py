#!/usr/bin/env python3
"""Check the typed read-site contract without generating a global C++ header."""
import argparse
import json
from pathlib import Path
import re

from flag_census import inventory

ROOT = Path(__file__).resolve().parents[2]
KINDS = {"Flag", "Presence", "Int", "Long", "Double", "Boolean",
         "Path", "ProfilePath", "Period", "Capacity", "Moduli", "Projection"}


def validate(root: Path = ROOT):
    catalog = json.loads((root / "src/base/controls.json").read_text())
    names, declared = set(), set()
    for entry in catalog["controls"]:
        name = entry["name"]
        if not re.fullmatch(r"[A-Z][A-Z0-9_]*", name) or name in names:
            raise ValueError("invalid or duplicate control " + name)
        names.add(name)
        if entry.get("legacy_text") or not entry["reads"]:
            raise ValueError("unreviewed or empty control " + name)
        for read in entry["reads"]:
            kind = read["kind"]
            if set(read) != {"kind"} or kind not in KINDS:
                raise ValueError("invalid read declaration for " + name)
            if (name, kind) in declared:
                raise ValueError("duplicate read mode for " + name)
            declared.add((name, kind))
    if (root / "src/base/ControlCatalog.h").exists():
        raise ValueError("retired global ControlCatalog.h remains")
    audit = inventory(root)
    if any("typed_kind" in read for read in audit["dynamic_reads"]):
        raise ValueError("typed controls require literal names and explicit modes")
    actual = {(entry["name"], site["reader"])
              for entry in audit["controls"] for site in entry["sites"]}
    unexpected = actual - declared
    unused = declared - actual
    if unexpected:
        raise ValueError("undeclared or mismatched read modes: " + repr(sorted(unexpected)))
    if unused:
        raise ValueError("control declarations have no reader: " + repr(sorted(unused)))
    return audit


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    try:
        audit = validate()
    except (ValueError, KeyError) as error:
        raise SystemExit(str(error)) from error
    print(f'{audit["unique_controls"]} controls / {audit["literal_read_sites"]} sites; '
          'typed source contract consistent; no generated C++ catalog')


if __name__ == "__main__":
    main()
