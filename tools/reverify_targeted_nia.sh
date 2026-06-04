#!/usr/bin/env bash
# Re-verify the targeted_nia corpus against the current binary.
# Usage: tools/reverify_targeted_nia.sh [timeout_secs] [out.tsv]
# Output columns: key  oracle  was  now  rc  wallclock_ms
set -u
TIMEOUT=${1:-15}
OUT=${2:-/tmp/targeted_nia_reverify.tsv}
BIN=build/bin/xolver
MANIFEST=targeted_nia/MANIFEST.tsv

printf 'key\toracle\twas\tnow\trc\twallclock_ms\n' > "$OUT"

# Skip header line; iterate
tail -n +2 "$MANIFEST" | awk -F'\t' '{print $5"\t"$6"\t"$7}' | while IFS=$'\t' read -r oracle was rel; do
  path="targeted_nia/$rel"
  [ -f "$path" ] || { printf '%s\tmissing\t%s\t%s\t-\t-\n' "$rel" "$oracle" "$was" >> "$OUT"; continue; }
  start=$(date +%s%3N)
  ( ulimit -v 3000000; timeout "${TIMEOUT}" "$BIN" solve "$path" < /dev/null ) > /tmp/_rv_out 2>/dev/null
  rc=$?
  out=$(head -1 /tmp/_rv_out)
  end=$(date +%s%3N)
  wall=$((end - start))
  verdict="$out"
  case "$verdict" in
    sat|unsat|unknown) ;;
    *) verdict="other:${verdict:0:20}" ;;
  esac
  if [ "$rc" = "124" ]; then verdict="timeout"; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$rel" "$oracle" "$was" "$verdict" "$rc" "$wall" >> "$OUT"
done

echo "wrote $OUT"
echo "summary:"
awk -F'\t' 'NR>1 {now[$4]++; if($4==$2) match_oracle++; if($4=="sat"||$4=="unsat") solved++; total++}
            END {for (k in now) printf "  %s: %d\n", k, now[k]; printf "  solved=%d/%d match_oracle=%d\n", solved, total, match_oracle}' "$OUT"
