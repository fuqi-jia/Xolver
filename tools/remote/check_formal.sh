#!/usr/bin/env bash
# Machine-check the mathematical certificate rules in staged Coq, on Panda1.
set -euo pipefail
cd "$(dirname "$0")/../.."
root="$PWD/dependencies/coq/root"
export COQLIB="$root/usr/lib/x86_64-linux-gnu/ocaml/5.4.0/coq"
export OCAMLPATH="$root/usr/lib/x86_64-linux-gnu/ocaml/5.4.0"
export OCAMLFIND_CONF="$root/etc/ocamlfind.conf"
# This single-domain proof does not need OCaml's default reservation for 128
# domains (which exceeds the EOS address-space limit before Coq even starts).
# https://ocaml.org/manual/5.4/runtime.html
export OCAMLRUNPARAM=d=1
label="${1:?validation label required}"
[[ "$label" =~ ^[A-Za-z0-9_.-]+$ ]] || exit 2
source_dir="${2:-proofs}"
out="$PWD/validation/$label"
mkdir -p build/coq validation
mkdir "$out"
cp "$0" "$out/check_formal.sh"
cp "$source_dir"/*.v "$out/"
exec 9>build/coq/.writer.lock
flock 9
cache="$PWD/build/coq"
"$root/usr/bin/coqc" --version > "$out/version.txt"
sha256sum "$out"/*.v "$root/usr/bin/coqc" "$root/usr/bin/coqchk" > "$out/hashes.txt"
coqc_rc=0
coqchk_rc=125
modules=()
set +e
for source in "$out"/*.v; do
    filename="$(basename "$source")"
    cp "$source" "$cache/$filename" || exit 1
    "$root/usr/bin/coqc" -R "$cache" Xolver "$cache/$filename" >> "$out/coqc.log" 2>&1
    coqc_rc=$?
    (( coqc_rc == 0 )) || break
    modules+=("Xolver.${filename%.v}")
done
if (( coqc_rc == 0 )); then
    "$root/usr/bin/coqchk" -silent -R "$cache" Xolver "${modules[@]}" > "$out/coqchk.log" 2>&1
    coqchk_rc=$?
    sha256sum "$cache"/*.vo > "$out/compiled.sha256"
fi
set -e
python3 - "$out" "$coqc_rc" "$coqchk_rc" <<'PY'
import json, os, pathlib, sys
root = pathlib.Path(sys.argv[1])
metrics = {"coqc_rc": int(sys.argv[2]), "coqchk_rc": int(sys.argv[3]),
           "closed_theorems": (root / "coqc.log").read_text().count("Closed under the global context")}
(root / "metrics.json").write_text(json.dumps(metrics) + "\n")
if os.environ.get("EOS_METRICS_FILE"):
    pathlib.Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(metrics) + "\n")
PY
(( coqc_rc == 0 && coqchk_rc == 0 ))
