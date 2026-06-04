#!/usr/bin/env bash
# Run BLAN over the targeted_nia corpus only (no xolver — avoids CPU contention).
# Usage: tools/blan_only_corpus.sh [timeout_secs] [out.tsv]
# Columns: key  oracle  was  blan  blan_ms  blan_vars  blan_clauses
set -u
TIMEOUT=${1:-15}
OUT=${2:-/tmp/blan_only.tsv}
BLAN=/mnt/d/D_Study/BUAA/projects/BLAN/BLAN
MANIFEST=/mnt/d/D_Study/BUAA/projects/NLColver/targeted_nia/MANIFEST.tsv

printf 'key\toracle\twas\tblan\tblan_ms\tblan_vars\tblan_clauses\n' > "$OUT"

tail -n +2 "$MANIFEST" | awk -F'\t' '{print $5"\t"$6"\t"$7}' | while IFS=$'\t' read -r oracle was rel; do
    path="/mnt/d/D_Study/BUAA/projects/NLColver/targeted_nia/$rel"
    [ -f "$path" ] || continue
    start=$(date +%s%3N)
    ( ulimit -v 3000000; timeout "${TIMEOUT}" "$BLAN" "$path" < /dev/null ) > /tmp/_v.out 2>/dev/null
    rc=$?
    end=$(date +%s%3N)
    wall=$((end - start))
    # BLAN prints verdict on the last (non-DIAG) line; DIAG line has "satVars=N clauses=M".
    verdict=$(grep -v '^\[BLAN-DIAG\]' /tmp/_v.out | tail -1)
    vars=$(grep '^\[BLAN-DIAG\]' /tmp/_v.out | tail -1 | sed -nE 's/.*satVars=([0-9]+).*/\1/p')
    clauses=$(grep '^\[BLAN-DIAG\]' /tmp/_v.out | tail -1 | sed -nE 's/.*clauses=([0-9]+).*/\1/p')
    if [ "$rc" = "124" ]; then verdict="timeout"; fi
    case "$verdict" in sat|unsat|unknown|timeout) ;; *) verdict="other" ;; esac
    [ -z "$vars" ] && vars="-"
    [ -z "$clauses" ] && clauses="-"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$rel" "$oracle" "$was" "$verdict" "$wall" "$vars" "$clauses" >> "$OUT"
done

echo "wrote $OUT"
awk -F'\t' 'NR>1 {
    tot++;
    b[$4]++;
    if ($4==$2) b_ok++;
}
END {
    printf "BLAN matches oracle: %d/%d\n", b_ok, tot;
    for (k in b) printf "  blan[%s]=%d\n", k, b[k];
}' "$OUT"
