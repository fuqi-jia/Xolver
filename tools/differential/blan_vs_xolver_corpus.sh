#!/usr/bin/env bash
# Run BLAN + xolver over the targeted_nia corpus; tabulate per-case verdict.
# Usage: tools/blan_vs_xolver_corpus.sh [timeout_secs] [out.tsv]
# Columns: key  oracle  was  blan  xolver  blan_ms  xolver_ms
set -u
TIMEOUT=${1:-15}
OUT=${2:-/tmp/blan_vs_xolver.tsv}
BLAN=/mnt/d/D_Study/BUAA/projects/BLAN/BLAN
XOL=/mnt/d/D_Study/BUAA/projects/NLColver/build/bin/xolver
MANIFEST=/mnt/d/D_Study/BUAA/projects/NLColver/targeted_nia/MANIFEST.tsv

run_one() {
    local solver_bin="$1" file="$2"
    local start end verdict
    start=$(date +%s%3N)
    ( ulimit -v 3000000; timeout "${TIMEOUT}" "$solver_bin" solve "$file" < /dev/null ) > /tmp/_v.out 2>/dev/null
    local rc=$?
    end=$(date +%s%3N)
    verdict=$(head -1 /tmp/_v.out 2>/dev/null)
    if [ "$rc" = "124" ]; then verdict="timeout"; fi
    case "$verdict" in sat|unsat|unknown|timeout) ;; *) verdict="other" ;; esac
    echo "${verdict}|$((end - start))"
}
run_blan_one() {
    local file="$1" start end verdict
    start=$(date +%s%3N)
    ( ulimit -v 3000000; timeout "${TIMEOUT}" "$BLAN" "$file" < /dev/null ) > /tmp/_v.out 2>/dev/null
    local rc=$?
    end=$(date +%s%3N)
    verdict=$(tail -1 /tmp/_v.out 2>/dev/null)
    if [ "$rc" = "124" ]; then verdict="timeout"; fi
    case "$verdict" in sat|unsat|unknown|timeout) ;; *) verdict="other" ;; esac
    echo "${verdict}|$((end - start))"
}

printf 'key\toracle\twas\tblan\txolver\tblan_ms\txolver_ms\n' > "$OUT"

tail -n +2 "$MANIFEST" | awk -F'\t' '{print $5"\t"$6"\t"$7}' | while IFS=$'\t' read -r oracle was rel; do
    path="/mnt/d/D_Study/BUAA/projects/NLColver/targeted_nia/$rel"
    [ -f "$path" ] || continue
    IFS='|' read -r b_v b_ms < <(run_blan_one "$path")
    IFS='|' read -r x_v x_ms < <(run_one "$XOL" "$path")
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$rel" "$oracle" "$was" "$b_v" "$x_v" "$b_ms" "$x_ms" >> "$OUT"
done

echo "wrote $OUT"
awk -F'\t' 'NR>1 {
    tot++;
    b[$4]++; x[$5]++;
    if ($4==$2) b_ok++;
    if ($5==$2) x_ok++;
    if ($4==$2 && $5!=$2) blan_only++;
    if ($5==$2 && $4!=$2) xol_only++;
}
END {
    printf "BLAN matches oracle: %d/%d\n", b_ok, tot;
    printf "xolver matches oracle: %d/%d\n", x_ok, tot;
    printf "BLAN-only wins: %d\n", blan_only;
    printf "xolver-only wins: %d\n", xol_only;
    for (k in b) printf "  blan[%s]=%d\n", k, b[k];
    for (k in x) printf "  xolver[%s]=%d\n", k, x[k];
}' "$OUT"
