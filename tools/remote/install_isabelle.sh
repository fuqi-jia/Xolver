#!/usr/bin/env bash
# One persistent, checksum-pinned proof-assistant installation on the server.
set -euo pipefail
cd /pub/data/jiafq/xolver
root="$PWD/dependencies/isabelle"
mkdir -p "$root"
exec 9>"$root/.install.lock"
flock 9
release=Isabelle2025-2
digest=a20a507bc7c1270d8be96a9f3fbec06345387789d2dc2c4d3df6260d47bfb33c
archive="$root/${release}_linux.tar.gz"
url="https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/${release}_linux.tar.gz"
if [[ ! -f "$archive" ]]; then
    curl --fail --location --continue-at - --retry 3 --connect-timeout 30 \
        --output "$archive.partial" "$url"
    printf '%s  %s\n' "$digest" "$archive.partial" | sha256sum --check
    mv "$archive.partial" "$archive"
fi
printf '%s  %s\n' "$digest" "$archive" | sha256sum --check
if [[ ! -f "$root/installed.json" ]]; then
    tar -xzf "$archive" -C "$root"
fi
"$root/$release/bin/isabelle" version
python3 - "$root" "$release" "$digest" "$url" <<'PY'
import json, os, pathlib, sys
root, release, digest, url = pathlib.Path(sys.argv[1]), *sys.argv[2:]
record = dict(release=release, archive_sha256=digest, source=url)
(root / "installed.json").write_text(json.dumps(record, indent=2) + "\n")
out = pathlib.Path("validation/isabelle-install")
out.mkdir(parents=True, exist_ok=True)
(out / "provenance.json").write_text(json.dumps(record, indent=2) + "\n")
metrics = dict(installed=1, archive_verified=1)
(out / "metrics.json").write_text(json.dumps(metrics) + "\n")
if os.environ.get("EOS_METRICS_FILE"):
    pathlib.Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(metrics) + "\n")
PY
