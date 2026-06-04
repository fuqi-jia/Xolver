#!/usr/bin/env bash
# Run the held-out set through xolver under a named env profile and tabulate.
# Usage: tools/heldout_validate.sh <profile_label> <env_string> [timeout_s] [out.tsv]
# Example: tools/heldout_validate.sh kstep1 'XOLVER_NIA_BITBLAST_K_STEP=1' 15 /tmp/heldout_kstep1.tsv
set -u
LABEL=${1:?profile label}
ENVS=${2-}
TIMEOUT=${3:-15}
OUT=${4:-/tmp/heldout_${LABEL}.tsv}
LIST=${HELDOUT_LIST:-/tmp/heldout_paths.txt}
XOL=/mnt/d/D_Study/BUAA/projects/NLColver/build/bin/xolver

printf 'profile\tkey\toracle_sat\tverdict\trc\twallclock_ms\n' > "$OUT"
while read -r path; do
    [ -f "$path" ] || continue
    start=$(date +%s%3N)
    ( ulimit -v 3000000; eval "env $ENVS timeout ${TIMEOUT} $XOL solve '$path' < /dev/null" ) > /tmp/_h.out 2>/dev/null
    rc=$?
    end=$(date +%s%3N)
    wall=$((end - start))
    verdict=$(head -1 /tmp/_h.out 2>/dev/null)
    if [ "$rc" = "124" ]; then verdict="timeout"; fi
    case "$verdict" in sat|unsat|unknown|timeout) ;; *) verdict="other:${verdict:0:30}" ;; esac
    printf '%s\t%s\tsat\t%s\t%s\t%s\n' "$LABEL" "$path" "$verdict" "$rc" "$wall" >> "$OUT"
done < "$LIST"

echo "wrote $OUT"
echo "summary:"
awk -F'\t' 'NR>1 {h[$4]++; tot++; if($4=="sat") sat++} END {printf "  sat=%d/%d\n", sat+0, tot; for(k in h) printf "  %s: %d\n", k, h[k]}' "$OUT"
