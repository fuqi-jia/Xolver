#!/usr/bin/env bash
set -uo pipefail
cd "$(dirname "$0")/../.."
label="${1:-proofs}"
[[ "$label" =~ ^[A-Za-z0-9_.-]+$ ]] || exit 2
out="$PWD/validation/$label"
mkdir -p "$out"
XOLVER_PROOF_TIMEOUT=30 XOLVER_PROOF_WORKDIR="$out/artifacts" \
    bash tools/proof/run_proof_corpus.sh "${XOLVER_PROOF_SOLVER:-$PWD/validation/candidate/xolver}" \
    "$PWD/dependencies/checkers/drat-trim/drat-trim" \
    docs/audit/evidence/proof-corpus.txt > "$out/corpus.log" 2>&1
rc=$?
python3 - "$rc" "$out" <<'PY'
import json, os, pathlib, re, sys
out=pathlib.Path(sys.argv[2])
text=(out / 'corpus.log').read_text()
m=re.search(r'VERIFIED\(complete\)=(\d+)\s+VERIFIED-SKELETON\(lemmas assumed\)=(\d+)\s+NO-PROOF\(degraded\)=(\d+)\s+SKIP\(not-unsat\)=(\d+)\s+REJECTED=(\d+)\s+ERROR=(\d+)',text)
metrics={'proof_rc':int(sys.argv[1])}
if m: metrics.update(zip(['cnf_complete','skeleton','no_proof','skip','rejected','errors'],map(int,m.groups())))
(out / 'metrics.json').write_text(json.dumps(metrics)+'\n')
if os.environ.get('EOS_METRICS_FILE'):
    pathlib.Path(os.environ['EOS_METRICS_FILE']).write_text(json.dumps(metrics)+'\n')
PY
exit "$rc"
